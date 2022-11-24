{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

--import Control.Monad
import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe, catMaybes )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, elabTypeWithTag, elabDecl)
import Optimize ( optimize )
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl, ppTypeSyn )
import MonadFD4
import TypeChecker ( tc, tcDecl )
import CEK (search, toTTerm)
import Bytecompile (bytecompileModule, bcWrite, showBC, bcRead, runBC)
import ClosureConvert (runCC, cWrite)
import System.FilePath (dropExtension)
import C (ir2C)

prompt :: String
prompt = "FD4> "



-- | Parser de banderas
parseMode :: Parser (Mode,Bool)
parseMode = (,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
      <|> flag' CEK (long "cek" <> short 'p' <> help "Ejecutar en la CEK")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   -- reemplazar por la siguiente línea para habilitar opción
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool, [FilePath])
parseArgs = (\(a,b) c -> (a,b,c)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2022" )

    go :: (Mode,Bool,[FilePath]) -> IO ()
    go (InteractiveCEK,opt,files) =
              runOrFail (Conf opt InteractiveCEK) (runInputT defaultSettings (repl files))
    go (Interactive,opt,files) =
              runOrFail (Conf opt Interactive) (runInputT defaultSettings (repl files))
    go (RunVM, opt, files) =
              runOrFail (Conf opt RunVM) $ mapM_ runBytecodeFromFile files 
    go (m,opt, files) =
              runOrFail (Conf opt m) $ mapM_ compileFile files

runBytecodeFromFile :: MonadFD4 m => FilePath -> m ()
runBytecodeFromFile f = do
  bc <- liftIO $ bcRead f
  runBC bc
  return ()

runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compileFile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compileFile ::  MonadFD4 m => FilePath -> m ()
compileFile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    modu <- mapM handleDecl decls
    m <- getMode
    case m of
      Bytecompile -> do
        code <- bytecompileModule $ catMaybes modu
        printFD4 $ showBC code
        liftIO $ bcWrite code (dropExtension f ++ ".bc")
      CC -> do
        let codigoC = (ir2C . runCC . catMaybes) modu
        printFD4 codigoC
        liftIO $ cWrite codigoC (dropExtension f ++ ".c")
      _ -> return ()
    setInter i

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

handleAdd :: MonadFD4 m => (TTerm -> m TTerm) -> SDecl -> m (Maybe (Decl TTerm))
handleAdd evalF d@LetDecl {} = do
      elabbed <- elabDecl d
      (Decl p x ty tt) <- tcDecl elabbed
      o <- getOpt
      tt' <- if o then optimize tt else return tt
      te <- evalF tt'
      addDecl (Decl p x ty te)
      return $ Just $ Decl p x ty te
handleAdd _ (TypeDecl pos s st) = do
      st' <- elabTypeWithTag s st
      addTypeSyn (s, st')
      return Nothing

handleDecl ::  MonadFD4 m => SDecl -> m (Maybe (Decl TTerm))
handleDecl d = do
        m <- getMode
        case m of
          Interactive -> handleAdd eval d
          Typecheck -> do
              f <- getLastFile
              printFD4 ("Chequeando tipos de "++f)
              case d of
                LetDecl {} -> do
                  elabbed <- elabDecl d
                  (Decl p x ty tt) <- tcDecl elabbed
                  o <- getOpt
                  td <- if o then optimize tt else return tt
                  let tdDecl = Decl p x ty td
                  addDecl tdDecl
                  ppterm <- ppDecl tdDecl
                  printFD4 ppterm
                  return Nothing
                t@(TypeDecl pos s st) -> do
                  st' <- elabTypeWithTag s st
                  addTypeSyn (s, st')
                  ppterm <- ppTypeSyn t
                  printFD4 ppterm
                  return Nothing
          InteractiveCEK -> handleAdd (\tt -> do {te <- search tt [] []; return $ toTTerm te}) d
          CEK -> handleAdd (\tt -> do {te <- search tt [] []; return $ toTTerm te}) d
          Bytecompile -> handleAdd return d
          CC -> handleAdd return d
          RunVM -> do
            return Nothing
          Eval -> handleAdd eval d
              -- opt <- getOpt
              -- td' <- if opt then optimize td else td

data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do
                      printFD4 "---Declaraciones de términos---"  
                      printFD4 (unlines (reverse (nub (map declName glb))))
                      printFD4 "---Sinónimos de tipos---"
                      printFD4 (unlines (reverse (nub (map fst glbTy))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compileFile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compileFile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> void $ handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         m <- getMode
         case m of
           InteractiveCEK -> do
            te <- search tt [] []
            ppte <- pp (toTTerm te)
            printFD4 (ppte ++ " : " ++ ppTy (getTy tt))
           _ -> do
            te <- eval tt
            ppte <- pp te
            printFD4 (ppte ++ " : " ++ ppTy (getTy tt))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)
