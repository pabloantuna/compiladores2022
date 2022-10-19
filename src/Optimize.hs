module Optimize (optimize) where

import Lang
import MonadFD4
import Eval (semOp)
import Subst (subst)

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize m = inlineExpansion m >>= peephole consFold

inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion = return

consFold :: MonadFD4 m => TTerm -> m TTerm -- Asume que ya fueron foldeadas las subexpresiones
consFold b@(V (p, _) (Global n)) = do -- Si el global es una constante, lo propagamos
    t <- lookupDecl n
    case t of
      Nothing -> failPosFD4 p "Global no encontrado"
      Just a@(Const _ (CNat x)) -> return a
      Just _ -> return b
consFold (BinaryOp x0 bo t (Const _ (CNat 0))) = return t -- Caso x + 0 o x - 0
consFold (BinaryOp x0 Add (Const _ (CNat 0)) t') = return t' -- Caso 0 + x
consFold (BinaryOp x0 Sub c@(Const _ (CNat 0)) t) -- Caso 0 - x, que es siempre 0 porque solo hay numeros positivos
 | noEffects t = return c -- Si tiene efectos no se puede hacer
consFold (BinaryOp x0 op (Const _ (CNat x)) (Const _ (CNat y))) = return $ Const x0 (CNat (semOp op x y))
consFold (IfZ x0 (Const p (CNat 0)) t t') = return t -- Caso if con condicion 0 constante
consFold (IfZ x0 (Const p (CNat _)) t t') = return t' -- Caso if con condicion >0 constante
consFold (Let x0 s ty c@(Const _ _) sc) = peephole consFold $ subst c sc -- Let constante, sustituimos a manopla
consFold t = return t -- No hacemos nada xd

peephole :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> m TTerm
peephole f v@(V x0 var) = f v
peephole f c@(Const x0 co) = f c
peephole f (Lam x0 s ty (Sc1 t)) = peephole f t >>= f . Lam x0 s ty . Sc1
peephole f (App x0 t t') = do
    tOpt <- peephole f t
    t'Opt <- peephole f t'
    f (App x0 tOpt t'Opt)
peephole f (Print x0 s t) = peephole f t >>= f . Print x0 s
peephole f (BinaryOp x0 bo t t') = do
    tOpt <- peephole f t
    t'Opt <- peephole f t'
    f (BinaryOp x0 bo tOpt t'Opt)
peephole f (Fix x0 s ty str ty' (Sc2 t)) = peephole f t >>= f . Fix x0 s ty str ty' . Sc2
peephole f (IfZ x0 t t' t'') = do
    tOpt <- peephole f t
    t'Opt <- peephole f t'
    t''Opt <- peephole f t''
    f (IfZ x0 tOpt t'Opt t''Opt)
peephole f (Let x0 s ty t (Sc1 t')) = do
    tOpt <- peephole f t
    t'Opt <- peephole f t'
    f (Let x0 s ty tOpt (Sc1 t'Opt))

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
    case (s, tLeft, tRight) of
        (_, x, Const _  (CNat 0)) -> return x
        (Add, Const _  (CNat 0), x) -> return x
        (Sub, Const _  (CNat 0), x)
         | noEffects x -> return (Const p (CNat 0))
        (_, Const _ (CNat x), Const _ (CNat y)) -> return $ Const p (CNat $ semOp s x y)
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

noEffects :: TTerm -> Bool
noEffects (V x0 (Bound n)) = True
noEffects (V x0 (Free s)) = True
noEffects (V x0 (Global s)) = False -- Se me ocurre que buscar en el entorno cuenta como efecto porque de hecho podría fallar?
noEffects (Const x0 co) = True
noEffects (Lam x0 s ty (Sc1 t)) = noEffects t
noEffects (App x0 t t') = all noEffects [t, t']
noEffects (Print x0 s tm') = False
noEffects (BinaryOp x0 bo t t') = all noEffects [t, t']
noEffects (Fix x0 s ty str ty' sc) = False -- En realidad no sabemos, pero como los fix pueden llegar a tener divergencia por las dudas
noEffects (IfZ x0 t t' t'') = all noEffects [t, t', t'']
noEffects (Let x0 s ty t (Sc1 t')) = all noEffects [t, t']
