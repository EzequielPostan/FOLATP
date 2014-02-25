module Src.Parser
 ( formula
 , readFormula
 ) where

import Src.AST
import Parsing
import Data.Char

{-
     Este módulo contiene el parser de las fórmulas de la lógica de primer orden.
     Ante la falta de paréntesis, se utiliza la siguiente precedencia y 
     asociatividad 
    
      operador       símbolo  asociatividad
    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
      negación       ~        asocia a derecha  
      conjunción     &        asociativa, asocia a derecha 
      disyunción     |        asociativa, asocia a derecha 
      implicancia    =>       no asociativa, asocia a izquierda
      equivalencia   ==       asociativa, asocia a derecha 
-}

{- Parser para las fórmulas lógicas de primer orden -}
readFormula  :: String -> Maybe Form
readFormula s = case parse formula s of
    [(x,[])] -> Just x
    _        -> Nothing

{-
   Parser para fórmulas.
   Las fórmulas pueden ser predicados, formulas conectadas por 
   operadores lógicos y cuantificadores.
-}
formula :: Parser Form
formula  = token equa

{- La equivalencia tiene la menor precedencia y es asociativa -}
equa :: Parser Form
equa  = do x <- impl
           do (symbol "==" +++ symbol "<=>")
              y <- equa
              return (Eq x y)
            +++ return x

{- La implicancia asocia a izquierda -}
impl :: Parser Form
impl  = do x <- disj
           impl' x

impl'  :: Form -> Parser Form
impl' x = do (symbol "=>" +++ symbol "->")
             y <- disj
             impl' (Imp x y)
           +++ return x

{- La disyunción es asociativa -}
disj :: Parser Form
disj  = do x <- conj
           do symbol "|"
              y <- disj
              return (Or x y)
            +++ return x

{- La conjunción es asociativa-}
conj :: Parser Form
conj  = do x <- lite
           do symbol "&"
              y <- conj
              return (And x y)
            +++ return x

{- Un literal es un predicado negado o sin negar -}
lite :: Parser Form
lite  = do symbol "~"
           x <- lite
           return (Not x)
         +++ atom

{- Un átomo es un predicado sin negar -}
atom :: Parser Form
atom  = do p <- predicate
           do xs <- parenth (list term)
              return (Pred p xs)
            +++ return (Pred p [])
         +++ parenth formula
         +++ bracket quant

{- Una proposición cuantificada se encierra entre corchetes -}
quant :: Parser Form
quant  = do symbol "\\forall "
            v <- variable
            symbol ":"
            f <- formula
            return (Forall v f)
          +++ do symbol "\\exists "
                 v <- variable
                 symbol ":"
                 f <- formula
                 return (Exists v f)

{- 
   Parser para términos.
   Un término puede ser una variable, una constantes o una
   función aplicada a un número positivo de términos.
-}
term :: Parser Term
term  = do v <- variable
           do xs <- parenth (list term)
              return (Func v xs)
            +++ return (Var v)
         +++ do c <- constant
                return (Const c)


{- Predicados y Constantes -}
predicate :: Parser String
predicate  = do p <- upper
                ps <- many letter
                return (p:ps)

constant :: Parser String
constant  = predicate

{- Variables y Funciones -}
variable :: Parser String
variable  = many1 lower

{- Parser para elementos entre paréntesis -}
parenth  :: Parser a -> Parser a
parenth p = do symbol "("
               x <- token p
               symbol ")"
               return x

{- Parser para elementos entre corchetes -}
bracket  :: Parser a -> Parser a
bracket p = do symbol "["
               x <- token p
               symbol "]"
               return x

{- Parser para una lista de elementos separados por un coma -}
list  :: Parser a -> Parser [a]
list p = do x <- p
            do symbol ","
               xs <- list p
               return (x:xs)
             +++ return [x]
 
