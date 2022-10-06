{-# LANGUAGE PatternSynonyms #-}

{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Binary(put, get), decode, encode, Word8, putWord8, getWord8 )
import Data.Binary.Get ( isEmpty)

import Data.List (intercalate, unfoldr)
import Data.Char
import Eval (semOp)
import Subst (close)
import Data.Bits (shiftR, Bits (..), (.&.))

type Opcode = Word8
type Bytecode = [Word8]

newtype Bytecode8 = BC {un8 :: [Word8]}

instance Binary Bytecode8 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
                      BC xs <- go
                      return $ BC (x:xs)

data Val = I Int | Fun Env Bytecode | RA Env Bytecode
type Env = [Val]

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL     = 0
pattern RETURN   = 1
pattern CONST    = 2
pattern ACCESS   = 3
pattern FUNCTION = 4
pattern CALL     = 5
pattern ADD      = 6
pattern SUB      = 7
pattern JUMP     = 8
pattern FIX      = 9
pattern STOP     = 10
pattern SHIFT    = 11
pattern DROP     = 12
pattern PRINT    = 13
pattern PRINTN   = 14
pattern CJUMP    = 15
pattern TAILCALL = 16

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i1:i2:i3:i4:xs)     = ("CONST " ++  show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (ACCESS:i1:i2:i3:i4:xs)    = ("ACCESS " ++ show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (FUNCTION:i1:i2:i3:i4:xs)  = ("FUNCTION " ++ show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (JUMP:i1:i2:i3:i4:xs)      = ("JUMP " ++ show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (FIX:i1:i2:i3:i4:xs)  = ("FIX " ++ show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (CJUMP:i1:i2:i3:i4:xs)      = ("CJUMP " ++ show (bc2int [i1,i2,i3,i4])) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps xs
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound n)) = return $ ACCESS : int2bc n
bcc (V (p, _) (Free s)) = failPosFD4 p "Se encontró una variable libre compilando a bytecode"
bcc (V (p, _) (Global s)) = do
  d <- lookupDecl s
  case d of
    Nothing -> failPosFD4 p $ "No existe la variable global " ++ show s
    Just tm -> bcc tm
bcc (Const _ (CNat c)) = return $ CONST : int2bc c
bcc (Lam _ _ _ (Sc1 t)) = do
  bt <- bccT t
  return $ (FUNCTION : int2bc (length bt)) ++ bt
bcc (App _ t t') = do
  bt <- bcc t
  bt' <- bcc t'
  return $ bt ++ bt' ++ [CALL]
bcc (Print _ s t) = do
  bt <- bcc t
  return $ bt ++ [PRINT] ++ string2bc s ++ [NULL] ++ [PRINTN]
bcc (BinaryOp _ Add t t') = (\x y -> x ++ y ++ [ADD]) <$> bcc t <*> bcc t'
bcc (BinaryOp _ Sub t t') = (\x y -> x ++ y ++ [SUB]) <$> bcc t <*> bcc t'
bcc (Fix _ _ _ _ _ (Sc2 t)) = do
  bt <- bccT t
  return $ (FIX : int2bc (length bt)) ++ bt
bcc (IfZ _ cond thenT elseT) = do
  bcond <- bcc cond
  bthen <- bcc thenT
  belse <- bcc elseT
  -- La idea es que CJUMP saque lo que está en la pila, y si es distinto de 0 entonces salta tantas posiciones como lo dice en el proximo byte
  return $ bcond ++ (CJUMP : int2bc (length bthen + 5)) ++ bthen ++ (JUMP : int2bc (length belse)) ++ belse
bcc (Let _ _ _ def (Sc1 body)) = do
  bdef <- bcc def
  bbody <- bcc body
  return $ bdef ++ [SHIFT] ++ bbody ++ [DROP]

bccT :: MonadFD4 m => TTerm -> m Bytecode
bccT = bccGeneral [TAILCALL] [RETURN]

bccS :: MonadFD4 m => TTerm -> m Bytecode
bccS = bccGeneral [CALL, STOP] [STOP]

bccGeneral :: MonadFD4 m => Bytecode -> Bytecode -> TTerm -> m Bytecode
bccGeneral call end (App _ t t') = do
  bt <- bcc t
  bt' <- bcc t'
  return $ bt ++ bt' ++ call
bccGeneral call end (IfZ _ cond thenT elseT) = do
  bcond <- bcc cond
  bthen <- bccGeneral call end thenT
  belse <- bccGeneral call end elseT
  -- La idea es que CJUMP saque lo que está en la pila, y si es distinto de 0 entonces salta tantas posiciones como lo dice en el proximo byte
  return $ bcond ++ (CJUMP : int2bc (length bthen)) ++ bthen ++ belse
bccGeneral call end (Let _ _ _ def (Sc1 body)) = do
  bdef <- bcc def
  bbody <- bccGeneral call end body
  return $ bdef ++ [SHIFT] ++ bbody
bccGeneral call end t = do
  bt <- bcc t
  return $ bt ++ end

fillWith0 :: Bytecode -> Bytecode
fillWith0 b@[_, _, _, _] = b
fillWith0 b@(x:xs) = fillWith0 (b++[0])
fillWith0 [] = [0,0,0,0]

int2bc :: Int -> Bytecode
int2bc n = fillWith0 $ unfoldr step n
  where
    step 0 = Nothing
    step i = Just (fromIntegral i, i `shiftR` 8)

bc2int :: Bytecode -> Int
bc2int = foldr unstep 0
  where
    unstep b a = a `shiftL` 8 .|. fromIntegral b

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = concatMap (toUTF8 . ord)

toUTF8 :: Int -> [Word8]
toUTF8 n
 | n < 0x7F = [fromIntegral n]
 | n < 0x7FF = [0xC0 .|. (fromIntegral (n `shiftR` 6) .&. 0x1F), 0x80 .|. (fromIntegral n .&. 0x3F)]
 | n < 0xFFFF = [0xE0 .|. (fromIntegral (n `shiftR` 12) .&. 0x0F), 0x80 .|. (fromIntegral (n `shiftR` 6) .&. 0x3F), 0x80 .|. (fromIntegral n .&. 0x3F)]
 | otherwise = [0xF0 .|. (fromIntegral (n `shiftR` 18) .&. 0x07), 0x80 .|. (fromIntegral (n `shiftR` 12) .&. 0x3F), 0x80 .|. (fromIntegral (n `shiftR` 6) .&. 0x3F), 0x80 .|. (fromIntegral n .&. 0x3F)]

bc2string :: Bytecode -> String
bc2string (x:xs)
 | testBit x 7 && testBit x 6 && not (testBit x 5) = let b2:bs = xs in chr ((fromIntegral (x .&. 0x1F) `shiftL` 6) .|. fromIntegral (b2 .&. 0x3F)) : bc2string bs
 | testBit x 7 && testBit x 6 && testBit x 5 && not (testBit x 4) = let b2:b3:bs = xs in chr (((fromIntegral (x .&. 0x0F) `shiftL` 12) .|. fromIntegral (b2 .&. 0x3F) `shiftL` 6) .|. fromIntegral (b3 .&. 0x3F)) : bc2string bs
 | testBit x 7 && testBit x 6 && testBit x 5 && testBit x 4 && not (testBit x 3) = let b2:b3:b4:bs = xs in chr (fromIntegral (x .&. 0x07) `shiftL` 18 .|. fromIntegral (b2 .&. 0x3F) `shiftL` 12 .|. fromIntegral (b3 .&. 0x3F) `shiftL` 6 .|. fromIntegral (b3 .&. 0x3F)) : bc2string bs
 | otherwise = chr (fromIntegral x) : bc2string xs
bc2string [] = []

global2Free :: Var -> Var
global2Free (Global s) = Free s
global2Free x = x

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = do
  bccS $ toLets $ map (fmap $ fmap global2Free) m

toLets :: Module -> TTerm
toLets [] = error "que monada"
toLets [Decl p s ty t] = t
toLets ((Decl p s ty t) : des) = Let (p, getTy t) s ty t (close s $ toLets des)

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un8) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC = runBC' [] []

runBC' :: MonadFD4 m => [Val] -> Env -> Bytecode -> m ()
runBC' s e [] = failFD4 "Che maestro el bytecode me lo mandas por encomienda o que onda?"
runBC' (v : RA e c : s) _ (RETURN:xs) = runBC' (v : s) e c
runBC' s e (CONST:i1:i2:i3:i4:xs) = runBC' (I (bc2int [i1, i2, i3, i4]) : s) e xs
runBC' s e (ACCESS:i1:i2:i3:i4:xs) = runBC' ((e !! bc2int [i1, i2, i3, i4]) : s) e xs
runBC' s e (FUNCTION:i1:i2:i3:i4:xs) = runBC' (Fun e (take (bc2int [i1, i2, i3, i4]) xs) : s) e (drop (bc2int [i1, i2, i3, i4]) xs)
runBC' (v : Fun ef cf : s) e (CALL:xs) = runBC' (RA e xs : s) (v : ef) cf
runBC' (I y : I x : s) e (ADD:xs) = runBC' (I (semOp Add x y) : s) e xs
runBC' (I y : I x : s) e (SUB:xs) = runBC' (I (semOp Sub x y) : s) e xs
runBC' s e (JUMP:i1:i2:i3:i4:xs) = runBC' s e (drop (bc2int [i1, i2, i3, i4]) xs)
runBC' s e (FIX:i1:i2:i3:i4:xs) = runBC' (Fun efix (take (bc2int [i1, i2, i3, i4]) xs) : s) e (drop (bc2int [i1, i2, i3, i4]) xs)
  where efix = Fun efix (take (bc2int [i1, i2, i3, i4]) xs) : e
runBC' s e (STOP:xs) = printFD4 "The End"
runBC' (I n : s) e (CJUMP:i1:i2:i3:i4:xs)
 | n == 0 = runBC' s e xs
 | otherwise = runBC' s e (drop (bc2int [i1, i2, i3, i4]) xs)
runBC' (v : s) e (SHIFT:xs) = runBC' s (v : e) xs
runBC' s (v : e) (DROP:xs) = runBC' s e xs
runBC' s e (PRINT:xs) = let (str, _:rest) = span (/= NULL) xs in printFD4 (bc2string str) >> runBC' s e rest
runBC' s@(I n : _) e (PRINTN:xs) = printFD4 (show n) >> runBC' s e xs
runBC' (v : Fun ef cf : s) e (TAILCALL:xs) = runBC' s (v : ef) cf
runBC' s e (x:xs) = failFD4 "Amigo qué me mandaste"
