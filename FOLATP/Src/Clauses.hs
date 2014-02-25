{-# LANGUAGE TypeSynonymInstances #-}

module Src.Clauses
 ( Literal(..)
 , Tree
 , Resol
 , BinTree(..)
 , isAtom
 , literalName
 , Clause
 , ClauseSet
) where

import Pretty
import Src.AST
import Data.Set (Set, toAscList)

{- Estructura de datos para representar literales -}
data Literal = Atom String [Term]
             | Neg  String [Term]
    deriving (Show, Eq, Ord)

{- Función que indica si un literal es positivo -}
isAtom :: Literal -> Bool
isAtom (Atom _ _) = True
isAtom _          = False

{- Función que devuelve el nombre de un Literal-}
literalName :: Literal -> String
literalName (Atom p _) = p
literalName (Neg  p _) = p

{- Sinónimo de tipo que representa una cláusula -}
type Clause  = Set Literal

{- Sinónimo de tipo que representa un conjunto de cláusulas -}
type ClauseSet = Set Clause

{- Instancia del PrettyShow para un Literal -}
instance PrettyShow Literal where
--  pShow :: Literal -> String
    pShow (Atom p []) = p
    pShow (Atom p ts) = p ++ withPar (pList ", " "" ts)
    pShow (Neg  p []) = "~" ++ p
    pShow (Neg  p ts) = "~" ++ p ++ withPar (pList ", " "" ts)

{- Instancia del PrettyShow para una Cláusula -}
instance PrettyShow Clause where
--  pShow :: Clause -> String
    pShow set = let xs = toAscList set
                in case xs of
                    [] -> "{}"
                    _  -> "{" ++ pList ", " "" xs ++ "}"

{- Instancia del PrettyShow para un conjunto de cláusulas -}
instance PrettyShow ClauseSet where
--  pShow :: ClauseSet -> String
    pShow set = let xs = toAscList set
                in case xs of
                    [] -> "{}\n"
                    _  -> "{\n\t" ++ pList ",\n\t" "" xs ++ "\n}\n"

{- Estructura de datos para los árboles binarios -}
data BinTree a = Leaf | Node a (BinTree a) (BinTree a)

{- Sinónimo de tipo de árbol de cláusulas -}
type Tree = BinTree Clause
{- Sinónimo de tipo de conjunto de árboles de cláusulas -}
type Resol = Set Tree

{- Instancia de igualdad que sólo compara la raíz -}
instance Eq Tree where
--  (==) :: Tree -> Tree -> Bool
    Leaf == Leaf = True
    (Node x _ _) == (Node y _ _) = x == y

{- Instancia de orden que sólo compara la raíz -}
instance Ord Tree where
--  compare :: Tree -> Tree -> Ordering
    compare Leaf Leaf = EQ
    compare Leaf (Node _ _ _) = LT
    compare (Node _ _ _) Leaf = GT
    compare (Node a _ _) (Node b _ _) = compare a b

{- Instancia del PrettyShow para un árbol de cláusulas -}
instance PrettyShow Tree where
--  pShow :: Tree -> String
    pShow tree = showTree [] tree

{- Imprime un árbol binario
 Left = True; Right = False
-}
showTree :: (PrettyShow a) => [Bool] ->  BinTree a -> String
showTree [] Leaf = error "Error árbol vacío"
showTree _  Leaf = error "Error interno"
showTree bs (Node n Leaf Leaf) = prefixNode bs ++  pShow n ++ "\n"
showTree _  (Node _ Leaf _) = "Error árbol no binario"
showTree _  (Node _ _ Leaf) = "Error árbol no binario"
showTree bs (Node n l r) =
    prefixNode bs ++ pShow n ++ "\n"
    ++ prefix bs ++ "│\n"
    ++ showTree (True : bs) l
    ++ prefix bs ++ "│\n"
    ++ showTree (False : bs) r

prefixNode :: [Bool] -> String
prefixNode [] = ""
prefixNode (True  : bs) = prefix bs ++ "├─ "
prefixNode (False : bs) = prefix bs ++ "└─ "

prefix :: [Bool] -> String
prefix [] = ""
prefix (True  : bs) = prefix bs ++ "│ "
prefix (False : bs) = prefix bs ++ "  "

