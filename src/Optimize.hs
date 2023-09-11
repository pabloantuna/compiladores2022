module Optimize (optimize) where

import Eval (semOp)
import Lang
import MonadFD4
import Subst (open, close, close2, open2, subst)
import Common (Pos)

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize = topDown inline >=> bottomUp consFold

inline :: MonadFD4 m => TTerm -> m TTerm
inline t@(Let _ _ _ def body)
 | shouldInline t = inline $ subst def body
inline a@(App {}) = do
  return $ applyBodyArgs (getBody a)
inline t = return t

shouldInline :: TTerm -> Bool
shouldInline (Let _ _ _ def body) = noEffects def && termSize def < 60 -- este numero hacia que ande bien tests/ok/30-opt/incs_fun.fd4
shouldInline t = False

-- | La info del App y lo que se le estaba aplicando a la funcion
type AppInfo = ((Pos, Ty), TTerm)

-- | La info del Lam, y el nombre y tipo de la variable
type ArgInfo = ((Pos, Ty), Name, Ty)

-- | Nos devuelve el cuerpo de la funcion de muchos argumentos, con una lista de expresiones que se están aplicando y de los args de la funcion
getBody :: TTerm -> (TTerm, [AppInfo], [ArgInfo])
getBody = getBody' [] []
  where
    getBody' :: [AppInfo] -> [ArgInfo] -> TTerm -> (TTerm, [AppInfo], [ArgInfo])
    getBody' apps args a@(App x0 t t') = getBody' ((x0, t'):apps) args t
    getBody' apps args l@(Lam x0 s ty sc) = getBody' apps ((x0, s, ty):args) (open s sc)
    -- getBody' apps args l@(Fix x0 f fty x xty sc) = getBody' apps (l:args) (open2 f x sc)
    getBody' apps args t = (t, reverse apps, args)

-- | Convierte la función de varios argumentos a una serie de lets y substituciones. Si sobran apps o args restaura las aplicaciones y lambdas
applyBodyArgs :: (TTerm, [AppInfo], [ArgInfo]) -> TTerm
applyBodyArgs (t, [], []) = t
applyBodyArgs (t, apps, args)
 | length args > length apps = Lam x1 s ty (close s (applyBodyArgs (t, apps, restArgs)))
 | length args < length apps = App x0 (applyBodyArgs (t, restApps, args)) t'
 | noEffects t' = applyBodyArgs (subst t' (close s t), restApps, restArgs)
 | otherwise = applyBodyArgs (Let x1 s ty t' (close s t), restApps, restArgs)
   where
    ((x0, t'):restApps) = apps
    ((x1, s, ty):restArgs) = args


termSize :: TTerm -> Int
termSize (V x0 var) = 1
termSize (Const x0 co) = 1
termSize (Lam x0 s ty (Sc1 t)) = 1 + termSize t
termSize (App x0 t t') = 1 + termSize t + termSize t'
termSize (Print x0 s t) = 1 + termSize t
termSize (BinaryOp x0 bo t t') = 1 + termSize t + termSize t'
termSize (Fix x0 s ty str ty' (Sc2 t)) = 1 + termSize t
termSize (IfZ x0 t t' t'') = 1 + termSize t + termSize t' + termSize t''
termSize (Let x0 s ty t (Sc1 t')) = 1 + termSize t + termSize t'

consFold :: MonadFD4 m => TTerm -> m TTerm -- Asume que ya fueron foldeadas las subexpresiones (pensado para bottomUp)
consFold b@(V (p, _) (Global n)) = do
  -- Si el global es una constante, lo propagamos
  t <- lookupDecl n
  case t of
    Nothing -> failPosFD4 p "Global no encontrado"
    Just a@(Const _ (CNat x)) -> return a
    Just _ -> return b
consFold (BinaryOp x0 Add (BinaryOp x1 Add t t') t'') = do -- (x + y) + z = x + (y + z) nos deja foldear mas constantes
  tt <- consFold (BinaryOp x1 Add t' t'') 
  consFold $ BinaryOp x0 Add t tt
consFold (BinaryOp x0 Sub (BinaryOp x1 Sub t t') t'') = do -- (x - y) - z = x - (y + z) nos deja foldear mas constantes
  tt <-  consFold (BinaryOp x1 Add t' t'') 
  consFold $ BinaryOp x0 Sub t tt
consFold (BinaryOp x0 Sub (BinaryOp _ Add t (Const x1 (CNat y))) (Const _ (CNat z)))
 | y < z = consFold $ BinaryOp x0 Sub t (Const x1 (CNat $ z - y)) -- (x + y) - z = x - (z - y) cuando y < z
 | otherwise = consFold $ BinaryOp x0 Add t (Const x1 (CNat $ y - z)) -- (x + y) - z = x + (y - z) cuando z < y
-- Notar que no se puede hacer nada (creo) cuando tenemos primero la resta y después la suma
consFold (BinaryOp x0 bo t (Const _ (CNat 0))) = return t -- Caso x + 0 o x - 0
consFold (BinaryOp x0 Add (Const _ (CNat 0)) t') = return t' -- Caso 0 + x
consFold (BinaryOp x0 Sub c@(Const _ (CNat 0)) t) -- Caso 0 - x, que es siempre 0 porque solo hay numeros positivos
  | noEffects t = return c -- Si tiene efectos no se puede hacer
consFold (BinaryOp x0 op (Const _ (CNat x)) (Const _ (CNat y))) = return $ Const x0 (CNat (semOp op x y)) -- caso dos constantes (x+y) o (x-y)
consFold (IfZ x0 (Const p (CNat 0)) t t') = return t -- Caso if con condicion 0 constante
consFold (IfZ x0 (Const p (CNat _)) t t') = return t' -- Caso if con condicion >0 constante
consFold (Let x0 s ty def@(Const _ _) body) = bottomUp consFold $ subst def body -- Let constante, sustituimos a manopla
consFold (BinaryOp x0 Add t'@(Const _ (CNat _)) t) = consFold $ BinaryOp x0 Add t t'
consFold (BinaryOp x0 Add t (BinaryOp x1 Add t' c@(Const _ _))) = return $ BinaryOp x0 Add (BinaryOp x1 Add t t') c
consFold t = return t -- No hacemos nada xd

applyInside :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> m TTerm -- es como si fuera un fmap loco
applyInside m (Lam x0 s ty sc) = Lam x0 s ty <$> (close s <$> m (open s sc))
applyInside m (App x0 tm tm') = App x0 <$> m tm <*> m tm'
applyInside m (Print x0 s tm) = Print x0 s <$> m tm
applyInside m (BinaryOp x0 bo tm tm') = BinaryOp x0 bo <$> m tm <*> m tm'
applyInside m (Fix x0 s ty str ty' sc) = Fix x0 s ty str ty' <$> (close2 s str <$> m (open2 s str sc))
applyInside m (IfZ x0 tm tm' tm2) = IfZ x0 <$> m tm <*> m tm' <*> m tm2
applyInside m (Let x0 s ty tm sc) = Let x0 s ty <$> m tm <*> (close s <$> m (open s sc))
applyInside m x = return x

topDown :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> m TTerm
topDown f = f >=> applyInside (topDown f)

bottomUp :: MonadFD4 m => (TTerm -> m TTerm) -> TTerm -> m TTerm
bottomUp f = applyInside (bottomUp f) >=> f

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
