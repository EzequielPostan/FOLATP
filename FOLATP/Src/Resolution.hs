module Src.Resolution
 ( Result
 , resolution
 ) where

import Src.Clauses
import Src.Unification
import Src.AST
import Src.Standardize
import qualified Data.Set as Set
import Monads
import Data.List (sort)

{- Tipo devuelto por el algoritmo de resolución:
 + Left Nothing, significa que el conjunto de cláusulas es satisfacible.
 + Left (Just tree), significa que el conjunto de cláusulas es insatisfacible,
     y tree será el árbol que genera la cláusula vacía.
 + Right set, significa que todavía no se pudo generar la cláusula vacía,
     y set es el conjunto de cláusulas generadas hasta el momento. -}
type Result = Either (Maybe Tree) Resol

{- Toma dos conjunto de cláusulas, premisas y conclusión negada.
Los convierte a conjuntos de árboles y aplica el algoritmo de resolución -}
resolution :: ClauseSet -> ClauseSet -> Result
resolution conc prem = let xs = Set.mapMonotonic (\x -> Node x Leaf Leaf) conc
                           ys = Set.mapMonotonic (\x -> Node x Leaf Leaf) prem
                       in resolve1 xs ys

{- Toma dos conjuntos de árboles (cláusulas).
El conjunto new contiene sólo las nuevas cláusulas generadas en el paso anterior
y el conjunto old tiene todo el resto de las cláusulas.
Se generan todas las cláusulas nuevas posibles en new' y se llama recursivamente -}
resolve1 :: Resol -> Resol -> Result
resolve1 new old = do new' <- resolve2 new old
                      let old'  = Set.union old new
                      let new'' = Set.difference new' old'
                      if new'' == Set.empty then Left Nothing
                       else resolve1 new'' old'

{- Genera todas las cláusulas resolventes posibles combinando
 dos cláusulas de new o una cláusula de new y una de old -}
resolve2 :: Resol -> Resol -> Result
resolve2 new old | new == Set.empty = return Set.empty
                 | otherwise        = 
    let (t, new') = Set.deleteFindMin new
        c  = case t of
              Leaf        -> error "Error interno: árbol hoja en resolve2"
              Node r _ _  -> append "y" r
        ts = Set.union new' old
    in do r1 <- resolve3 (t,c) ts
          r2 <- resolve2 new' old
          return (Set.union r1 r2)

{- Genera el conjunto de todas las cláusulas resolventes al convinar 
c1 (raíz normalizada de t1) con cada una de las cláusulas de ts -}
resolve3 :: (Tree,Clause) ->  Resol -> Result
resolve3 (t1,c1) ts | ts == Set.empty = return Set.empty
                    | otherwise       = 
      let (t2, ts') = Set.deleteFindMin ts
      in case t2 of
          Leaf        -> error "Error interno: árbol hoja en resolve3"
          Node c2 _ _ -> do r1 <- resolve4 (t1,c1) (t2,c2)
                            r2 <- resolve3 (t1,c1) ts'
                            return (Set.union r1 r2)

{- Toma dos cláusulas y devuelve el conjunto de todas las
 cláusulas resolventes que se puedan generar a partir de estas -}
resolve4 :: (Tree,Clause) -> (Tree,Clause) -> Result
resolve4 (t1,c1) (t2,c2) = 
    let (p1, n1) = span isAtom (Set.toAscList c1)
        (p2, n2) = span isAtom (Set.toAscList c2)
    in do r1 <- unify (p1, n2) (n1 ++ p2) (t1, t2)
          r2 <- unify (p2, n1) (n2 ++ p1) (t1, t2)
          return (Set.union r1 r2)

type Pair a = (a, a)

{- unify toma un par de cláusulas representadas como listas de literales ordenadas lexicográficamente.
Los literales de la primer lista son positivos y los de la segunda lista son negativos.
Como segundo argumento toma una lista con el resto de los literales que formarían la cláusula resolvente.
Por último toma un par de árboles que serán los padres de la posible nueva cláusula.
Intenta unificar literales de la primer lista con los de la segunda. -}
unify :: Pair [Literal] -> [Literal] -> Pair Tree -> Result
-- si alguna de las listas es vacía no hay nada que unificar
unify ([], _) _ _ = return Set.empty
unify (_, []) _ _ = return Set.empty
-- en otro caso, intentamos la unificación recorriendo las listas
unify (Atom p xs : ps, Neg q ys : qs) rest (t1, t2) =
    if p < q then 
{- no voy a poder unificar p pues cada literar de ns es mayor que q, entonces, paso p a rest y sigo probando -}
        unify (ps, Neg q ys : qs) (Atom p xs : rest) (t1, t2)
    else if q < p then
{- no voy a poder unificar q pues cada literal de ps es mayor que q, entonces, paso q a rest y sigo probando -}
        unify (Atom p xs : ps, qs) (Neg q ys : rest) (t1, t2)
    else  -- si son iguales
{- acá si podrían unificar -}
        let (ps', restP) = span (\x -> literalName x == q) (Atom p xs : ps)
            (qs', restQ) = span (\x -> literalName x == p) (Neg  q ys : qs)
        in do r1 <- unifyAux1 (ps', qs') (restP ++ restQ ++ rest) (t1, t2)
              r2 <- unify (restP, restQ) (ps' ++ qs' ++ rest) (t1, t2)
              return (Set.union r1 r2)

{- Toma dos listas de literales con el mismo nombre de predicado e intenta unificar.
Hacemos recursión sobre la primer lista primero y luego sobre la segunda -}
unifyAux1 :: Pair [Literal] -> [Literal] -> Pair Tree -> Result
unifyAux1 ([],_) _ _ = return Set.empty
unifyAux1 (Atom p xs : ps, qs) rest (t1,t2) = do r1 <- unifyAux2 xs qs (ps ++ rest) (t1,t2)
                                                 r2 <- unifyAux1 (ps,qs) (Atom p xs : rest) (t1,t2)
                                                 return (Set.union r1 r2)

unifyAux2 :: [Term] -> [Literal] -> [Literal] -> Pair Tree -> Result
unifyAux2 _ [] _ _ = return Set.empty
unifyAux2 xs (Neg q ys : qs) rest (t1, t2) =
    case unification xs ys of
        Nothing    -> unifyAux2 xs qs (Neg q ys : rest) (t1, t2)
        Just subst -> let clause = (standardize "x") . sort . (applySubst subst) $ (qs++rest)
                          tree   = Node (Set.fromAscList clause) t1 t2
                      in if clause == [] then
                             Left (Just tree)
                         else do
                             r1 <- factors clause clause (t1,t2)
                             r2 <- unifyAux2 xs qs (Neg q ys : rest) (t1, t2)
                             return (Set.insert tree (Set.union r1 r2))

{-  applySubst aplica una sustitución a una cláusula -}
applySubst :: Subst -> [Literal] -> [Literal] 
applySubst s [] = []
applySubst s (Atom n ts : xs) = Atom n (substitute s ts) : applySubst s xs
applySubst s (Neg n ts : xs) = Neg n (substitute s ts) : applySubst s xs

{- elimina elementos repetidos de una lista ordenada -}
elimRep :: Eq a => [a] -> [a]
elimRep []  = []
elimRep [x] = [x]
elimRep (y:x:xs) | x == y    = elimRep (x:xs)
                 | otherwise = y : elimRep (x:xs)

{- Además de agregar las resolventes al conjunto de cláusulas también debemos poner
todos sus factores. La siguiente función devuelve el conjunto de todos los factores
de una cláusula -}
factors :: [Literal] -> [Literal] -> Pair Tree -> Result
factors (Atom p xs : Atom q ys : ls) clause (t1,t2)
  | p == q = case unification xs ys of
               Nothing    -> factors (Atom q ys : ls) clause (t1,t2)
               Just subst -> do let clause' = (standardize "x") . elimRep . sort . (applySubst subst) $ clause
                                let tree'   = Node (Set.fromAscList clause') t1 t2
                                r1 <- factors (Atom q ys : ls) clause (t1,t2)
                                r2 <- factors clause' clause' (t1,t2)
                                return (Set.insert tree' (Set.union r1 r2))
  | otherwise = factors (Atom q ys : ls) clause (t1,t2)
factors (Neg  p xs : Neg  q ys : ls) clause (t1,t2)
  | p == q = case unification xs ys of
               Nothing    -> factors (Neg  q ys : ls) clause (t1,t2)
               Just subst -> do let clause' = (standardize "x") . elimRep . sort . (applySubst subst) $ clause
                                let tree'   = Node (Set.fromAscList clause') t1 t2
                                r1 <- factors (Neg  q ys : ls) clause (t1,t2)
                                r2 <- factors clause' clause' (t1,t2)
                                return (Set.insert tree' (Set.union r1 r2))
  | otherwise = factors (Neg  q ys : ls) clause (t1,t2)
factors [] _ _ = return Set.empty
factors (l : ls) clause (t1,t2) = factors ls clause (t1,t2)

