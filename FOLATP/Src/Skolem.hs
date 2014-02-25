module Src.Skolem
 ( skolem
 ) where

import Src.AST
import Src.Clauses
--import Control.Monad.State.Lazy
import Monads
import Data.Set (fromList)

{- Lleva una fórmula en forma prenex a su forma normal de skolem -}
skolem  :: Form -> State Int ClauseSet
skolem f = do f' <- elimQuan f []
              return (fromList . map fromList . distribute $ f')

{-
   Elimina los cuantificadores existenciales sustituyendo las 
   variables afectadas por funciones de skolem y elimina los 
   cuantificadores universales.
-}
elimQuan  :: Form -> [String] -> State Int Form
elimQuan (Forall u f) vs = elimQuan f (u:vs)
elimQuan (Exists u f) [] = do n <- get
                              put (n+1)
                              let f' = replace u (Const ("C"++show n)) f
                              elimQuan f' []
elimQuan (Exists u f) vs = do n <- get
                              put (n+1)
                              let f' = replace u (Func ("f"++show n) (map Var vs)) f
                              elimQuan f' vs
elimQuan f            _  = return f

{-
   Reemplaza en una fórmula todas las ocurrencias de una variable
   por un término determinado.
-}
replace :: String -> Term -> Form -> Form
replace v t (Forall u f) = Forall u $ replace v t f
replace v t (Exists u f) = Exists u $ replace v t f
replace v t (And p q)    = And (replace v t p) (replace v t q)
replace v t (Or  p q)    = Or  (replace v t p) (replace v t q)
replace v t (Not f)      = Not $ replace v t f
replace v t (Pred s xs)  = Pred s $ map (replaceTerm v t) xs
replace _ _ _            = error "Función elimQuan: constructor inesperado"

{-
   Reemplaza en un término todas las ocurrencias de una variable 
   por un término determinado.
-}
replaceTerm :: String -> Term -> Term -> Term
replaceTerm v t (Var u) | u == v    = t
                        | otherwise = Var u
replaceTerm v t (Const c)           = Const c
replaceTerm v t (Func s ts)         = Func s $ map (replaceTerm v t) ts

{- 
   Pasa a forma normal conjuntiva. La fórmula que toma no tiene
   ningún cuantificador. Devuelve un conjunto de cláusulas.
-}
distribute :: Form -> [[Literal]]
distribute (And p q)         = distribute p ++ distribute q
distribute (Or  p q)         = let ps = distribute p
                                   qs = distribute q
                               in distAux ps qs
distribute (Not (Pred s ts)) = [[Neg  s ts]]
distribute (Pred s ts)       = [[Atom s ts]]
distribute _                 = error "Función distribute: constructor inesperado"

{-
   Cada elemento de la primer lista se concatena con todos los
   elementos de la segunda lista. Luego se concatenan todos los
   resultados
-}
distAux :: [[a]] -> [[a]] -> [[a]]
distAux []       yss = []
distAux (xs:xss) yss = map (xs ++) yss ++ distAux xss yss
