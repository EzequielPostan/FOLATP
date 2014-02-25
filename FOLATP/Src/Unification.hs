module Src.Unification
 ( unification
 , Subst
 , substitute
 ) where

import Src.AST

{- Sinónimo de tipo para una sustitución -}
type Subst = [(Term, String)]

{-
   Intenta unificar dos listas de términos.
   Si las listas son unificables devuelve el unificador
   más general correspondiente, sino devulve Nothing.
   Nota: suponemos que ambas listas de términos tienen 
   la misma logitud.
-}
unification :: [Term] -> [Term] ->  Maybe Subst
unification xs ys = if length xs /= length ys 
                    then error "Error en unification: Predicados de mismo nombre y distinta aridad"
                    else unifAux xs ys []

{-
   Toma dos listas de términos que intentará unificar y
   una sustitución. Si las listas son unificables devuelve
   la composición de la sustitución proporcionada con el 
   unificador más general para los términos, sino devuelve
   Nothing.
-}
unifAux :: [Term] -> [Term] -> Subst -> Maybe Subst
unifAux []     []     s = Just s
unifAux (x:xs) (y:ys) s = case (x, y) of

  (Var v, Var u)         -> if u == v 
                            then unifAux xs ys s
                            else continue xs ys s [(y,v)] 

  (Var v, _)             -> if isVarInTerm v y
                            then Nothing
                            else continue xs ys s [(y,v)] 

  (_, Var u)             -> if isVarInTerm u x
                            then Nothing
                            else continue xs ys s [(x,u)]

  (Const a, Const b)     -> if a == b
                            then unifAux xs ys s
                            else Nothing

  (Const _, Func _ _)    -> Nothing

  (Func _ _, Const _)    -> Nothing

  (Func f ts, Func g us) -> if f == g
                            then case unification ts us of
                              Nothing -> Nothing
                              Just ns -> continue xs ys s ns
                            else Nothing
{-
   Toma una variable y un término y devuelve true sii
   la variable se encuentra en el término.
-}
isVarInTerm :: String -> Term -> Bool
isVarInTerm v (Var u)     = v == u
isVarInTerm v (Const _)   = False
isVarInTerm v (Func _ ts) = any (isVarInTerm v) ts

{-
   Toma dos términos y dos sustituciones s y ns.
   Le aplica a ambos términos la sustitución nueva ns,
   compone las dos sustituciones s y ns, e intenta unificar
   las dos nuevas listas de términos.
-}
continue :: [Term] -> [Term] -> Subst -> Subst -> Maybe Subst
continue xs ys s ns = let xs' = substitute ns xs
                          ys' = substitute ns ys
                          s'  = s +-+ ns
                      in unifAux xs' ys' s'

{-
   Aplica una sustitución a una lista de términos.
   Nota: toda la substitución se aplica de manera "simultánea".
-}
substitute :: Subst -> [Term] -> [Term]
substitute s ts = map (substTerm s) ts

{- Aplica una sustitución a un término -}
substTerm :: Subst -> Term -> Term
substTerm [] t            = t
substTerm ((u, x) : s) t = case t of
    Var v     -> if v == x then u else substTerm s (Var v)
    Const c   -> Const c
    Func f ls -> Func f $ substitute ((u, x) : s) ls
 
{- Compone dos sustituciones -}
(+-+) :: Subst -> Subst -> Subst
[] +-+ s2 = s2
s1 +-+ s2 = let (_, vs) = unzip s1
            in elimId (substAux s1 s2) ++ elimSubst vs s2

{-
   Toma dos sustituciones y le aplica la segunda sustitución
   a todos los términos en la primera sustitución
-}
substAux :: Subst -> Subst -> Subst 
substAux s1 s2 = let (ts, vs) = unzip s1
                 in zip (substitute s2 ts) vs

{- Elimina las sustituciones identidad -}
elimId :: Subst -> Subst
elimId []            = []
elimId ((t, x) : s) = case t of
    Var v  -> if x == v then elimId s else (t, x) : elimId s
    _      -> (t, x) : elimId s

{- Elimina las sustituciones de una lista de variables -}
elimSubst :: [String] -> Subst -> Subst 
elimSubst _ []               = []
elimSubst ts ((t, x) : s)    = if elem x ts
    then elimSubst ts s
    else (t, x) : elimSubst ts s
