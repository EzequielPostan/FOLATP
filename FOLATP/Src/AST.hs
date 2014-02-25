{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Src.AST
 ( Form(..)
 , Term(..)
 , Quant
 , UnOp
 , BinOp
 ) where

import Pretty

{-
    Este módulo contiene las estructuras que definen la gramática
    de la lógica de primer orden.
    Las funciones "pShow" utilizan la siguiente tabla de precedencia para
    evitar la impresión de paréntesis innecesarios

    operador       símbolo  asociatividad
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
    negación       ~        asocia a derecha  
    conjunción     &        es asociativa y no imprime paréntesis 
    disyunción     |        es asociativa y no imprime paréntesis 
    implicancia    =>       asocia a izquierda
    equivalencia   ==       es asociativa y no imprime paréntesis 
-}


{- Estructura de datos para las Fórmulas Lógicas -}
data Form	= Pred String [Term]
			| Not Form
			| And Form Form
			| Or  Form Form
			| Imp Form Form
			| Eq  Form Form
			| Forall String Form
			| Exists String Form
	deriving (Show, Eq)

{- Estructura de datos para los Términos -}
data Term 	= Var String
			| Const String
			| Func String [Term]
	deriving (Show, Eq, Ord)

{- Sinonimos de tipos para cuantificadores y operadores -}
type Quant = String -> Form -> Form
type UnOp  = Form -> Form
type BinOp = Form -> Form -> Form

{- Instancia del PreetyShow de las Fórmulas Lógicas -}
instance PrettyShow Form where
--	pShow             :: Form -> String
	pShow (Pred p [])  = p
	pShow (Pred p ts)  = p ++ withPar (pList ", " "" ts)

	pShow (Not p)      = let x = isAnd p || isOr p || isImp p || isEq p
	                     in pUn x "~" p

	pShow (And p q)    = let x = isOr p || isImp p || isEq p
	                         y = isOr q || isImp q || isEq q
	                     in pBin (x, y) " & " p q

	pShow (Or  p q)    = let x = isImp p || isEq p
	                         y = isImp q || isEq q
	                     in pBin (x, y) " | " p q

	pShow (Imp p q)    = let x = isEq p
	                         y = isImp q || isEq q
	                     in pBin (x, y) " => " p q

	pShow (Eq  p q)    = pBin (False, False) " == " p q

	pShow (Forall v f) = "[\\forall " ++ v ++ " : " ++ pShow f ++ "]"
	pShow (Exists v f) = "[\\exists " ++ v ++ " : " ++ pShow f ++ "]"

{- Instancia del PreetyShow de los Términos -}
instance PrettyShow Term where
--	pShow            :: Term -> String
	pShow (Var v)     = v
	pShow (Const c)   = c
	pShow (Func f ts) = f ++ withPar (pList ", " "" ts)

{- indica si la fórmula es una conjunción -}
isAnd          :: Form -> Bool
isAnd (And _ _) = True
isAnd _         = False

{- indica si la fórmula es una disyunción -}
isOr           :: Form -> Bool
isOr  (Or  _ _) = True
isOr  _         = False

{- indica si la fórmula es una implicancia -}
isImp          :: Form -> Bool
isImp (Imp _ _) = True
isImp _         = False

{- indica si la fórmula es una equivalencia -}
isEq           :: Form -> Bool
isEq  (Eq  _ _) = True
isEq  _         = False

