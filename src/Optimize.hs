module Optimize (optimize) where

import Lang
import MonadFD4
import Eval (semOp)
import PPrint (pp)
import Subst (subst)

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize m = inlineExpansion m >>= constantFolding >>= (\x -> pp x >>= printFD4 >> return x)

inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion = return

constantFolding :: MonadFD4 m => TTerm -> m TTerm
constantFolding b@(V (p, _) (Global n)) = do
    t <- lookupDecl n
    case t of
      Nothing -> failPosFD4 p "Global no encontrado"
      Just a@(Const _ (CNat x)) -> return a
      Just _ -> return b
constantFolding (BinaryOp p s t t') = do
    tLeft <- constantFolding t
    tRight <- constantFolding t'
    case (tLeft, tRight) of
        (Const _ (CNat x), Const _ (CNat y)) -> return $ Const p (CNat $ semOp s x y)
        _ -> return $ BinaryOp p s tLeft tRight
constantFolding (Lam a b c (Sc1 t)) = Lam a b c <$> (Sc1 <$> constantFolding t)
constantFolding (App a t t') = App a <$> constantFolding t <*> constantFolding t'
constantFolding (Print a b t) = Print a b <$> constantFolding t
constantFolding (Fix a b c d e (Sc2 t)) = Fix a b c d e <$> (Sc2 <$> constantFolding t)
constantFolding (IfZ a t t' t'') = do
    tCond <- constantFolding t
    case tCond of
        (Const _ (CNat 0)) -> constantFolding t'
        (Const _ (CNat x)) -> constantFolding t''
        _ -> IfZ a tCond <$> constantFolding t' <*> constantFolding t''
constantFolding (Let a b c t body@(Sc1 t')) = do
    tDef <- constantFolding t
    case tDef of
      Const p (CNat n) -> constantFolding $ subst tDef body
      _ -> Let a b c tDef <$> (Sc1 <$> constantFolding t')
constantFolding t = return t
