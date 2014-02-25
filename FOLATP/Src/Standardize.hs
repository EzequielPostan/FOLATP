module Src.Standardize 
 ( standardize
 , append
 ) where

import Src.AST
import Src.Clauses
import Monads
import qualified Data.Set as Set
import Data.List (elemIndex)

{- Antepone un string a cada variable de la cláusula para diferenciarlas de 
las variables de otras cláusulas -}
append :: String -> Clause -> Clause
append xs c = Set.mapMonotonic (appendLiteral xs) c

appendLiteral :: String -> Literal -> Literal
appendLiteral xs (Atom p ts) = Atom p (map (appendTerm xs) ts)
appendLiteral xs (Neg  p ts) = Neg  p (map (appendTerm xs) ts)

appendTerm :: String -> Term -> Term
appendTerm xs (Var ys)    = Var (xs++ys)
appendTerm _  (Const c)   = Const c
appendTerm xs (Func f ts) = Func f (map (appendTerm xs) ts)

{- Estandariza las variables de las distintas cláusulas -}
standardize    :: String -> [Literal] -> [Literal]
standardize xs c = fst $ runState (standClause xs c) (0, [])

{- Para estandarizar las variables en las distintas cláusulas usamos la mónada State.
En el estado llevamos un entero que indica los índices de las variables ya utilizadas
y la lista de las variables en la cláusula actual que ya aparecieron -}

standClause :: String -> [Literal] -> State (Int, [String]) [Literal]
standClause xs = mapM $ standLiteral xs 

standLiteral :: String ->  Literal -> State (Int, [String]) Literal
standLiteral xs (Atom p ts) = do ts' <- mapM (standTerm xs) ts
                                 return (Atom p ts')
standLiteral xs (Neg  p ts) = do ts' <- mapM (standTerm xs) ts
                                 return (Neg  p ts')

standTerm :: String -> Term -> State (Int, [String]) Term
standTerm xs (Var v)     = do
    (n, vs) <- get
    case elemIndex v vs of
        Nothing -> do put (n+1, v:vs)
                      return $ Var (xs ++ show (n+1))
        Just m  -> return $ Var (xs ++ show (n-m))
standTerm _ (Const c)   = return $ Const c
standTerm xs (Func f ts) = do ts' <- mapM (standTerm xs) ts
                              return (Func f ts')

