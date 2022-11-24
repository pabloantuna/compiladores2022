module Optimize (optimize) where

import Eval (semOp)
import Lang
import MonadFD4
import Subst (varChanger, subst')
import PPrint (pp)

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = peephole inlineExpansion >=> peephole consFold

inlineExpansion :: MonadFD4 m => TTerm -> m TTerm
inlineExpansion coso@(Let x0 s ty def body@(Sc1 t))
 | length calls == 1 || (isFunc def || noEffects def) && (termSize def < 20 && length calls < 5) = do
  -- pp coso >>= printFD4 . ("Inlineando : " ++)
  -- printFD4 ("llamadas de " ++ show s ++ ":")
  -- mapM_ (pp >=> printFD4) calls
  peephole inlineExpansion $ subst' (if isFix def then extractFixInvariant def else def) body
  where calls = getCalls 0 t
inlineExpansion (App x0 l@(Lam x1 s ty sc) v@(Const _ _)) = return (subst' v sc)
inlineExpansion (App x0 l@(Lam x1 s ty sc) arg) = return (Let x0 s (getTy arg) arg sc)
inlineExpansion (App x0 (Let x1 s ty tm (Sc1 t)) t') = Let x1 s ty tm <$> (Sc1 <$> inlineExpansion (App x0 t (arreglar t')))
inlineExpansion t = return t

isFunc :: TTerm -> Bool
isFunc (Lam {}) = True
isFunc (Fix {}) = True
isFunc _ = False

extractFixInvariant :: TTerm -> TTerm
extractFixInvariant = id

getCalls :: Int -> TTerm -> [TTerm]
getCalls d t@(V x0 (Bound n)) = [t | n == d] -- si queremos que cuente como una call cuando solamente se pone la funcion sin argumentos (por ahora ni idea)
getCalls d (V x0 var) = []
getCalls d (Const x0 co) = []
getCalls d (Lam x0 s ty (Sc1 t)) = getCalls (d+1) t
getCalls d t@(App x0 tm tm')
 | boundAtLeft d t = t:callsOnRights d t
 | otherwise = getCalls d tm ++ getCalls d tm'
getCalls d (Print x0 s t) = getCalls d t
getCalls d (BinaryOp x0 bo t t') = getCalls d t ++ getCalls d t'
getCalls d (Fix x0 s ty str ty' (Sc2 t)) = getCalls (d+2) t
getCalls d (IfZ x0 t t' t'') = getCalls d t ++ getCalls d t' ++ getCalls d t''
getCalls d (Let x0 s ty def (Sc1 body)) = getCalls d def ++ getCalls (d+1) body

boundAtLeft :: Int -> TTerm -> Bool
boundAtLeft d (App _ t t') = boundAtLeft d t
boundAtLeft d (V x0 (Bound n))
 | n == d = True
boundAtLeft d t = False

callsOnRights :: Int -> TTerm -> [TTerm]
callsOnRights d (App x0 t t') = callsOnRights d t ++ getCalls d t'
callsOnRights d t = []

termSize :: TTerm -> Int
termSize (V x0 var) = 1
termSize (Const x0 co) = 1
termSize (Lam x0 s ty (Sc1 t)) = 1 + termSize t
termSize (App x0 t t') = 1 + termSize t + termSize t'
termSize (Print x0 s t) = 1 + termSize t
termSize (BinaryOp x0 bo t t') = 1 + termSize t + termSize t'
termSize (Fix x0 s ty str ty' (Sc2 t)) = 1 + termSize t -- Me dan miedo los fix así que voy a hacer que cuenten como que son mas grandes
termSize (IfZ x0 t t' t'') = 1 + termSize t + termSize t' + termSize t''
termSize (Let x0 s ty t (Sc1 t')) = 1 + termSize t + termSize t'

arreglar :: TTerm -> TTerm
arreglar = varChanger (\_ p n -> V p (Free n)) (\d p i -> V p (Bound $ if i > d then i + 1 else i))

consFold :: MonadFD4 m => TTerm -> m TTerm -- Asume que ya fueron foldeadas las subexpresiones
consFold b@(V (p, _) (Global n)) = do
  -- Si el global es una constante, lo propagamos
  t <- lookupDecl n
  case t of
    Nothing -> failPosFD4 p "Global no encontrado"
    Just a@(Const _ (CNat x)) -> return a -- (x - 2) + 3
    Just _ -> return b
consFold (BinaryOp x0 Add (BinaryOp _ Add t (Const x1 (CNat y))) (Const _ (CNat z))) = return $ BinaryOp x0 Add t (Const x1 (CNat $ y + z)) -- (x + y) + z = x + (y + z) nos deja foldear mas constantes
consFold (BinaryOp x0 Sub (BinaryOp _ Sub t (Const x1 (CNat y))) (Const _ (CNat z))) = return $ BinaryOp x0 Sub t (Const x1 (CNat $ y + z)) -- (x - y) - z = x - (y + z) nos deja foldear mas constantes
consFold (BinaryOp x0 Sub (BinaryOp _ Add t (Const x1 (CNat y))) (Const _ (CNat z)))
 | y < z = return $ BinaryOp x0 Sub t (Const x1 (CNat $ z - y)) -- (x + y) - z = x - (z - y) cuando y < z
 | otherwise = return $ BinaryOp x0 Add t (Const x1 (CNat $ y - z)) -- (x + y) - z = x + (y - z) cuando z < y
-- Notar que no se puede hacer nada (creo) cuando tenemos primero la resta y después la suma
consFold (BinaryOp x0 bo t (Const _ (CNat 0))) = return t -- Caso x + 0 o x - 0
consFold (BinaryOp x0 Add (Const _ (CNat 0)) t') = return t' -- Caso 0 + x
consFold (BinaryOp x0 Sub c@(Const _ (CNat 0)) t) -- Caso 0 - x, que es siempre 0 porque solo hay numeros positivos
  | noEffects t = return c -- Si tiene efectos no se puede hacer
consFold (BinaryOp x0 op (Const _ (CNat x)) (Const _ (CNat y))) = return $ Const x0 (CNat (semOp op x y))
consFold (IfZ x0 (Const p (CNat 0)) t t') = return t -- Caso if con condicion 0 constante
consFold (IfZ x0 (Const p (CNat _)) t t') = return t' -- Caso if con condicion >0 constante
consFold (Let x0 s ty c@(Const _ _) sc) = peephole consFold $ subst' c sc -- Let constante, sustituimos a manopla
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

-- constantFolding :: MonadFD4 m => TTerm -> m TTerm
-- constantFolding b@(V (p, _) (Global n)) = do
--   t <- lookupDecl n
--   case t of
--     Nothing -> failPosFD4 p "Global no encontrado"
--     Just a@(Const _ (CNat x)) -> return a
--     Just _ -> return b
-- constantFolding (BinaryOp p s t t') = do
--   tLeft <- constantFolding t
--   tRight <- constantFolding t'
--   case (s, tLeft, tRight) of
--     (_, x, Const _ (CNat 0)) -> return x
--     (Add, Const _ (CNat 0), x) -> return x
--     (Sub, Const _ (CNat 0), x)
--       | noEffects x -> return (Const p (CNat 0))
--     (_, Const _ (CNat x), Const _ (CNat y)) -> return $ Const p (CNat $ semOp s x y)
--     _ -> return $ BinaryOp p s tLeft tRight
-- constantFolding (Lam a b c (Sc1 t)) = Lam a b c <$> (Sc1 <$> constantFolding t)
-- constantFolding (App a t t') = App a <$> constantFolding t <*> constantFolding t'
-- constantFolding (Print a b t) = Print a b <$> constantFolding t
-- constantFolding (Fix a b c d e (Sc2 t)) = Fix a b c d e <$> (Sc2 <$> constantFolding t)
-- constantFolding (IfZ a t t' t'') = do
--   tCond <- constantFolding t
--   case tCond of
--     (Const _ (CNat 0)) -> constantFolding t'
--     (Const _ (CNat x)) -> constantFolding t''
--     _ -> IfZ a tCond <$> constantFolding t' <*> constantFolding t''
-- constantFolding (Let a b c t body@(Sc1 t')) = do
--   tDef <- constantFolding t
--   case tDef of
--     Const p (CNat n) -> constantFolding $ subst' tDef body
--     _ -> Let a b c tDef <$> (Sc1 <$> constantFolding t')
-- constantFolding t = return t

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
