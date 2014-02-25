module Main where

import System.IO
--import Control.Monad.State.Lazy
import Monads
import Parsing
import Pretty
import Data.Char (isAlphaNum)
import qualified Data.Set as Set
import Src.AST
import Src.Parser
import Src.Resolution
import Src.Clauses
import Src.Prenex
import Src.Skolem

main :: IO ()
main  = do putStrLn ""
           putStrLn " Bienvenido al demostrador automático de teoremas de Logica de Primer Orden"
           putStrLn " Para ayuda, escriba 'help'"
           putStrLn ""
           evalStateT prompt ([],[])
           putStrLn " Adios!"

--------------------- usamos el transformador de mónadas StateT ----------------

type Pair a = (a,a)

prompt :: StateT (Pair [Form]) IO ()
prompt  = do lift $ putStr "> "
             lift $ hFlush stdout
             cmd <- lift getLine
             if cmd == "" then prompt
              else processCmd (parseCmd cmd)

{----------------------------- Tipos de comandos -------------------------------}
data What = All | KB | Query | Index Int | Sentence Form
        deriving Show

data Cmd = Error String
         | Help
         | Exit
         | Load FilePath What -- kb, query
         | Save FilePath What -- kb, query
         | Premise Form
         | Conclusion Form
         | Run (Maybe FilePath)
         | List What -- all, kb, query
         | Delete What -- all, kb, query, index
         | Prenex What -- all, kb, query, index, sentence
         | Skolem What -- all, kb, query, index, sentence
    deriving Show

{--------------------------- Procesado de los comandos -------------------------}

processCmd :: Cmd -> StateT (Pair [Form]) IO ()
processCmd (Error s)      = do lift $ putStrLn (" Comando '"++s++"' desconocido")
                               lift $ putStrLn " Para ayuda, escriba 'help'"
                               prompt

processCmd Help           = do lift $ putStrLn helpMessage
                               prompt

processCmd Exit           = return ()

processCmd (Load file w)  = do mSents <- lift $ withFile file ReadMode (getSents 0)
                               case mSents of
                                 Nothing    -> do lift $ putStrLn (" del archivo "++file)
                                                  lift $ putStrLn " Archivo no cargado"
                                                  prompt
                                 Just sents -> do (kb,query) <- get
                                                  lift $ putStrLn " Archivo cargado exitosamente"
                                                  (case w of
                                                     KB    -> put (kb++sents,query)
                                                     Query -> put (kb,query++sents)
                                                   ) >> prompt

processCmd (Save file w)  = do (kb,query) <- get
                               (case w of
                                  KB    -> lift $ withFile file AppendMode (putSents kb)
                                  Query -> lift $ withFile file AppendMode (putSents query)
                                ) >> prompt

processCmd (Premise s)    = do (kb,query) <- get
                               put (s:kb,query)
                               prompt

processCmd (Conclusion s) = do (kb,query) <- get
                               put (kb,Not s:query)
                               prompt

processCmd (List w)       = do (kb,query) <- get
                               (case w of
                                  All   -> do lift $ listSents kb 0
                                              lift $ putStrLn "----------------------------"
                                              lift $ listSents query (length kb)
                                  KB    -> lift $ listSents kb 0
                                  Query -> lift $ listSents query (length kb)
                                ) >> prompt

processCmd (Delete w)     = do (kb,query) <- get
                               let n = length kb
                               let m = n + length query
                               (case w of
                                  All     -> put ([],[])
                                  KB      -> put ([],query)
                                  Query   -> put (kb,[])
                                  Index i -> if i<1 then lift $ putStrLn " Indice incorrecto"
                                              else if i<=n then put (deleteAt (i-1) kb,query)
                                               else if i <= m then put (kb,deleteAt (i-n-1) query)
                                                else lift $ putStrLn " Indice incorrecto"
                                ) >> prompt

processCmd (Run mfile)    = do state <- get
                               lift (case solve state of
                                       Nothing   -> putStrLn " La implicación es FALSA"
                                       Just tree -> do putStrLn " La implicación es VERDADERA"
                                                       putStrLn ""
                                                       case mfile of
                                                         Nothing   -> putStrLn (pShow tree)
                                                         Just file -> writeFile file (pShow tree)
                                    ) >> prompt

processCmd (Prenex w)     = do (kb,query) <- get
                               let n = length kb
                               let m = n + length query
                               lift (case w of
                                       All        -> mapM_ prenexSent (kb++query)
                                       KB         -> mapM_ prenexSent kb
                                       Query      -> mapM_ prenexSent query
                                       Sentence f -> prenexSent f
                                       Index i    -> if i<1 then putStrLn " Indice incorrecto"
                                                      else if i<=n then prenexSent (kb !! (i-1))
                                                       else if i <= m then prenexSent (query !! (i-n-1))
                                                        else putStrLn " Indice incorrecto"
                                    ) >> prompt

processCmd (Skolem w)     = do (kb,query) <- get
                               let n = length kb
                               let m = n + length query
                               lift (case w of
                                       All        -> let cs  = skolemList (kb++query)
                                                         fcs = zip (kb++query) cs
                                                     in mapM_ skolemSent fcs
                                       KB         -> let cs  = skolemList kb
                                                         fcs = zip kb cs
                                                     in mapM_ skolemSent fcs
                                       Query      -> let cs  = skolemList query
                                                         fcs = zip query cs
                                                     in mapM_ skolemSent fcs
                                       Sentence f -> skolemSent (f,evalState (skolem . prenex $ f) 0)
                                       Index i    -> if i<1 then putStrLn " Indice incorrecto"
                                                      else if i<=n then do let f = kb!!(i-1)
                                                                           let c = evalState (skolem . prenex $ f) 0
                                                                           skolemSent (f,c)
                                                       else if i <= m then do let f = query!!(i-n-1)
                                                                              let c = evalState (skolem . prenex $ f) 0
                                                                              skolemSent (f,c)
                                                        else putStrLn " Indice incorrecto"
                                    ) >> prompt

{--------------- Funciones auxiliares para procesar los comandos ---------------}

deleteAt :: Int -> [a] -> [a]
deleteAt n xs = take n xs ++ drop (n+1) xs

getSents :: Int -> Handle -> IO (Maybe [Form])
getSents n h = do
  eof <- hIsEOF h
  if eof then return (Just [])
   else do
     line <- hGetLine h
     mfs  <- getSents (n+1) h
     case mfs of
       Nothing -> return Nothing
       Just fs -> case line of
                    ""      -> return (Just fs)
                    ('#':_) -> return (Just fs) -- comentario
                    _       -> case readFormula line of
                                 Just f  -> return (Just (f:fs))
                                 Nothing -> do putStr $ " Error en la línea "++show n
                                               return Nothing

putSents :: [Form] -> Handle -> IO ()
putSents [] h = return ()
putSents (f:fs) h = do
  hPutStrLn h (pShow f)
  putSents fs h

listSents :: [Form] -> Int -> IO ()
listSents [] _ = return ()
listSents (f:fs) n = do
  putStrLn (show (n+1) ++ ": " ++ pShow f)
  listSents fs (n+1)

solve :: Pair [Form] -> Maybe Tree
solve (kb,query) = let css = skolemList (kb ++ query)
                       (prem,conc) = splitAt (length kb) css
                   in case resolution (Set.unions conc) (Set.unions prem) of
                        Left resp -> resp
                        Right _   -> error "Error interno: debería continuar"

prenexSent :: Form -> IO ()
prenexSent f = do
  putStrLn ""
  putStrLn "Sentencia:"
  putStrLn (pShow f)
  putStrLn "Forma Prenex:"
  putStrLn (pShow (prenex f))

skolemList :: [Form] -> [ClauseSet]
skolemList fs = evalState (mapM (skolem . prenex) fs) 0

skolemSent :: (Form,ClauseSet) -> IO ()
skolemSent (f,c) = do
  putStrLn ""
  putStrLn "Sentencia:"
  putStrLn (pShow f)
  putStrLn "Forma Normal de Skolem:"
  putStrLn (pShow c)

{------------------------------ Mensaje de ayuda ------------------------------}
helpMessage :: String
helpMessage =
    "|======================================================================|\n" ++
    "| Los comandos disponibles son:                                        |\n" ++
    "|                                                                      |\n" ++
    "|   loadKB(FILE)     - Carga el archivo de sentencias FILE en KB.      |\n" ++ 
    "|   loadQuery(FILE)  - Carga el archivo de sentencias FILE en Query.   |\n" ++
    "|   saveKB(FILE)     - Guarda las sentencias de KB en FILE.            |\n" ++
    "|   saveQuery(FILE)  - Guarda las sentencias de Query en FILE.         |\n" ++
    "|   premise(SENT)    - Inserta la sentencia SENT en KB.                |\n" ++
    "|   conclusion(SENT) - Inserta la sentencia SENT en Query.             |\n" ++
    "|   run              - Prueba si la Query es implicada por la KB, y    |\n" ++
    "|                      muestra el resultado en la salida estándar.     |\n" ++
    "|   runTo(FILE)      - Igual que el comando anterior, pero guarda el   |\n" ++
    "|                      resultado en el archivo FILE.                   |\n" ++
    "|   listAll          - Lista todas las sentencias cargadas.            |\n" ++
    "|   listKB           - Lista las sentencias cargadas en KB.            |\n" ++ 
    "|   listQuery        - Lista las sentencias cargadas en Query.         |\n" ++
    "|   deleteAll        - Borra todas las sentencias cargadas.            |\n" ++
    "|   deleteKB         - Borra las sentencias cargadas en KB.            |\n" ++ 
    "|   deleteQuery      - Borra las sentencias cargadas en Query.         |\n" ++
    "|   delete(INT)      - Borra la sentencia ubicada en la posición INT.  |\n" ++
    "|   prenexAll        - Muestra la forma prenex de todas las sentencias |\n" ++
    "|                      almacenadas.                                    |\n" ++
    "|   prenexKB         - Muestra la forma prenex de las sentencias       |\n" ++
    "|                      almacenadas en KB.                              |\n" ++
    "|   prenexQuery      - Muestra la forma prenex de las sentencias       |\n" ++
    "|                      almacenadas en Query.                           |\n" ++
    "|   prenex(INT|SENT) - Muestra la forma prenex de la sentencia ubicada |\n" ++
    "|                      en la posición INT, o de la sentencia SENT,     |\n" ++
    "|                      según se indique.                               |\n" ++
    "|   skolemAll        - Muestra la forma normal de skolem de todas las  |\n" ++
    "|                      sentencias almacenadas.                         |\n" ++
    "|   skolemKB         - Muestra la forma normal de skolem de las        |\n" ++
    "|                      sentencias almacenadas en KB.                   |\n" ++
    "|   skolemQuery      - Muestra la forma normal de skolem de las        |\n" ++
    "|                      sentencias almacenadas en Query.                |\n" ++
    "|   skolem(INT|SENT) - Muestra la forma normal de skolem de la         |\n" ++
    "|                      sentencia ubicada en la posición INT, o de la   |\n" ++
    "|                      sentencia SENT, según se indique.               |\n" ++
    "|   exit             - Sale del programa.                              |\n" ++
    "|   help             - Imprime este mensaje.                           |\n" ++
    "|======================================================================|\n"

{--------------------------- Parser de los comandos ---------------------------}

parseCmd :: String -> Cmd
parseCmd s = case parse command s of
    [(cmd,[])] -> cmd
    _          -> Error s

command :: Parser Cmd
command  = token (chelp +++ cexit +++ creset +++ cload +++ csave +++
                  cpremise +++ cconclusion +++ crun +++ clist +++ cdelete +++
                  cprenex +++ cskolem)

chelp :: Parser Cmd
chelp  = do string "help"
            return Help

cexit :: Parser Cmd
cexit  = do string "exit"
            return Exit

creset :: Parser Cmd
creset  = do string "reset"
             return (Delete All)

cload :: Parser Cmd
cload  = do string "load"
            do string "KB"
               char '('
               p <- token path
               char ')'
               return (Load p KB)
             +++ do string "Query"
                    char '('
                    p <- token path
                    char ')'
                    return (Load p Query)

csave :: Parser Cmd
csave  = do string "save"
            do string "KB"
               char '('
               p <- token path
               char ')'
               return (Save p KB)
             +++ do string "Query"
                    char '('
                    p <- token path
                    char ')'
                    return (Save p Query)

path :: Parser String
path  = many1 (sat pathChar)
 where pathChar c =
         isAlphaNum c || 
         (c == '/') || 
         (c == '.') || 
         (c == '~')

cpremise :: Parser Cmd
cpremise  = do string "premise"
               char '('
               f <- token formula
               char ')'
               return (Premise f)

cconclusion :: Parser Cmd
cconclusion  = do string "conclusion"
                  char '('
                  f <- token formula
                  char ')'
                  return (Conclusion f)

crun :: Parser Cmd
crun  = do string "run"
           do string "To"
              char '('
              p <- token path
              char ')'
              return (Run (Just p))
            +++ return (Run Nothing)

clist :: Parser Cmd
clist  = do string "list"
            do string "All"
               return (List All)
             +++ do string "KB"
                    return (List KB)
                  +++ do string "Query"
                         return (List Query)

cdelete :: Parser Cmd
cdelete  = do string "delete"
              do string "All"
                 return (Delete All)
               +++ do string "KB"
                      return (Delete KB)
                    +++ do string "Query"
                           return (Delete Query)
                         +++ do char '('
                                i <- natural
                                char ')'
                                return (Delete (Index i))

cprenex :: Parser Cmd
cprenex  = do string "prenex"
              do string "All"
                 return (Prenex All)
               +++ do string "KB"
                      return (Prenex KB)
                    +++ do string "Query"
                           return (Prenex Query)
                         +++ do char '('
                                i <- natural
                                char ')'
                                return (Prenex (Index i))
                              +++ do char '('
                                     f <- token formula
                                     char ')'
                                     return (Prenex (Sentence f))

cskolem :: Parser Cmd
cskolem  = do string "skolem"
              do string "All"
                 return (Skolem All)
               +++ do string "KB"
                      return (Skolem KB)
                    +++ do string "Query"
                           return (Skolem Query)
                         +++ do char '('
                                i <- natural
                                char ')'
                                return (Skolem (Index i))
                              +++ do char '('
                                     f <- token formula
                                     char ')'
                                     return (Skolem (Sentence f))

