module Pretty
 ( PrettyShow
 , pShow
 , withPar
 , pUn
 , pBin
 , pList
 ) where

{- Clase para los tipos que tienen un show más elegante que el derivado -}
class PrettyShow a where
	pShow :: a -> String

{- imprime una cadena entre paréntesis -}
withPar  :: String -> String
withPar s = "(" ++ s ++ ")"

{- Imprime un operador unario y su argumento con o sin paréntesis según
 lo indique la variable booleana -}
pUn  :: (PrettyShow a) => Bool -> String -> a -> String
pUn True  op x = op ++ withPar (pShow x)
pUn False op x = op ++ pShow x

{- Imprime un operador binario infijo con sus dos argumentos, cada uno 
 con o sin paréntesis según indica la tupla de variables booleanas -}
pBin :: (PrettyShow a) => (Bool, Bool) -> String -> a -> a -> String
pBin (True , True ) op x y = withPar (pShow x) ++ op ++ withPar (pShow y)
pBin (True , False) op x y = withPar (pShow x) ++ op ++ pShow y
pBin (False, True ) op x y = pShow x ++ op ++ withPar (pShow y)
pBin (False, False) op x y = pShow x ++ op ++ pShow y

{- Toma una cadena "d" como delimitador, una cadena "e" para imprimir si 
 la lista es vacía y una lista "xs" de elementos. Imprime los elementos
 de la lista, separados por el delimitador "d" (si hay más de uno), o 
 imprime la cadena proporcionada "e" si la lista es vacía. -}
pList           :: (PrettyShow a) => String -> String -> [a] -> String
pList d e []     = e
pList d e [x]    = pShow x
pList d e (x:xs) = pShow x ++ d ++ pList d e xs
