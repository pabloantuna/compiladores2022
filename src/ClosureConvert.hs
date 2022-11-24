module ClosureConvert (runCC, cWrite) where

import IR
import Control.Monad.State (StateT (runStateT), get, put)
import Control.Monad.Writer
import Lang
import Subst (open, open2)

type CCMonad = StateT Int (Writer [IrDecl])

freshName :: String -> CCMonad String
freshName s = do
  i <- get
  put (i + 1)
  return (s ++ show i)

toLetsIR :: Name -> [(Name, Ty)] -> Ir -> Ir
toLetsIR = go 1
  where
    go :: Int -> Name -> [(Name, Ty)] -> Ir -> Ir
    go _ clos [] b = b
    go i clos ((n, ty):ns) b = IrLet n (getTyIR ty) (IrAccess (IrVar clos) (getTyIR ty) i) (go (i + 1) clos ns b) -- NO VA IRINT (NO ME IMPORTA)

substIR :: Name -> Ir -> Ir -> Ir
substIR n t (IrVar s)
 | n == s = t
substIR n t (IrGlobal s)
 | n == s = t
substIR n t (IrCall ir irs it) = IrCall (substIR n t ir) (map (substIR n t) irs) it
substIR n t (IrPrint s ir) = IrPrint s (substIR n t ir)
substIR n t (IrBinaryOp bo ir ir') = IrBinaryOp bo (substIR n t ir) (substIR n t ir')
substIR n t (IrLet s it ir ir') = IrLet s it (substIR n t ir) (substIR n t ir')
substIR n t (IrIfZ ir ir' ir'') = IrIfZ (substIR n t ir) (substIR n t ir') (substIR n t ir'')
substIR n t (MkClosure s irs) = MkClosure s (map (substIR n t) irs)
substIR n t (IrAccess ir it i) = IrAccess (substIR n t ir) it i
substIR _ _ x = x

getRetTyIR :: Ty -> IrTy
getRetTyIR (FunTy _ _ t) = getTyIR t
getRetTyIR (NatTy _) = undefined

getTyIR :: Ty -> IrTy
getTyIR (NatTy _) = IrInt
getTyIR (FunTy {}) = IrClo

closureConvert :: TTerm -> CCMonad Ir
closureConvert (V x0 (Bound n)) = undefined
closureConvert (V x0 (Free s)) = return $ IrVar s
closureConvert (V x0 (Global s)) = return $ IrGlobal s
closureConvert (Const x0 c) = return $ IrConst c
closureConvert t@(Lam (_, fty) s ty sc) = do
  n <- freshName ("lam_" ++ s)
  clos <- freshName "closure"
  let freeVs = freeVarsWithTypes t
  body <- closureConvert (open s sc)
  tell [IrFun n (getRetTyIR fty) [(clos, IrClo), (s, getTyIR ty)] (toLetsIR clos freeVs body)]
  return $ MkClosure n (map (IrVar . fst) freeVs)
closureConvert (App (_, ty) t t') = do
  clos <- freshName "app"
  def <- closureConvert t
  arg <- closureConvert t'
  return $ IrLet clos IrClo def (IrCall (IrAccess (IrVar clos) IrFunTy 0) [IrVar clos, arg] (getTyIR ty))
closureConvert (Print x0 s t) = do
  nam <- freshName "printN"
  bbbb <- closureConvert t
  return $ IrLet nam IrInt bbbb (IrPrint s (IrVar nam))
closureConvert (BinaryOp x0 bo t t') = do
  bt <- closureConvert t
  bt' <- closureConvert t'
  nameL <- freshName "boL"
  nameR <- freshName "boR"
  return $ IrLet nameL (getTyIR $ getTy t) bt (IrLet nameR (getTyIR $ getTy t') bt' $ IrBinaryOp bo (IrVar nameL) (IrVar nameR))
closureConvert t@(Fix x0 fn fty xn xty sc) = do
  n <- freshName ("fix_" ++ fn ++ "_" ++ xn)
  clos <- freshName "fixClosure"
  let freeVs = freeVarsWithTypes t
  body <- closureConvert (open2 fn xn sc)
  tell [IrFun n (getRetTyIR fty) [(clos, IrClo), (xn, getTyIR xty)] (IrLet fn (getTyIR fty) (IrVar clos) (toLetsIR clos freeVs body))]
  return $ MkClosure n (map (IrVar . fst) freeVs)
closureConvert (IfZ x0 t t' t'') = IrIfZ <$> closureConvert t <*> closureConvert t' <*> closureConvert t''
closureConvert (Let (pos, ty) s _ t sc) = IrLet s (getTyIR ty) <$> closureConvert t <*> closureConvert (open s sc)

ccDecl :: Decl TTerm -> CCMonad IrDecl
ccDecl (Decl p n t b) = IrVal n (getTyIR t) <$> closureConvert b

runCC :: [Decl TTerm] -> IrDecls
runCC ds = let ((decls, _), ccs) = runWriter (runStateT (mapM ccDecl ds) 0) in IrDecls (ccs ++ decls)

cWrite :: String -> FilePath -> IO ()
cWrite c filename = writeFile filename c