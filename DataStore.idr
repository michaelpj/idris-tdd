module Main

import Data.Vect

infixr 5 .+.

data Schema = SString
            | SInt
            | (.+.) Schema Schema

SchemaType: Schema -> Type
SchemaType SString = String
SchemaType SInt = Int
SchemaType (x .+. y) = (SchemaType x, SchemaType y)

record DataStore where
       constructor MkData
       schema : Schema
       size : Nat
       items : Vect size (SchemaType schema)

append: a -> Vect n a -> Vect (S n) a
append x [] = [x]
append x (y :: xs) = y :: append x xs

addToStore : (store : DataStore) -> SchemaType (schema store) -> DataStore
addToStore (MkData schema size items) newitem = MkData schema _ (append newitem items)

data Command: Schema -> Type where
     Add: SchemaType schema -> Command schema
     Get: Integer -> Command schema
     Quit: Command schema
     Size: Command schema
     Search: String -> Command schema
     SetSchema: (newSchema: Schema) -> Command schema

parseSchema : List String -> Maybe Schema
parseSchema ("String" :: xs) = case xs of
            [] => Just SString
            _ => do
                 xs_sch <- parseSchema xs
                 pure (SString .+. xs_sch)
parseSchema ("Int" :: xs) = case xs of
            [] => Just SInt
            _ => do 
                 xs_sch <- parseSchema xs
                 pure (SInt .+. xs_sch)
parseSchema _ = Nothing

parsePrefix : (schema : Schema) -> String -> Maybe (SchemaType schema, String)
parsePrefix SString input = getQuoted (unpack input)
            where
              getQuoted : List Char -> Maybe (String, String)
              getQuoted ('"' :: xs) = case span (/= '"') xs of
                          (quoted, '"' :: rest) => Just (pack quoted, ltrim (pack rest))
                          _ => Nothing
              getQuoted _ = Nothing
parsePrefix SInt input = case span isDigit input of
                          ("", rest) => Nothing
                          (num, rest) => Just (cast num, ltrim rest)
parsePrefix (lschema .+. rschema) input = do 
                     (l, rest) <- parsePrefix lschema input
                     (r, rest') <- parsePrefix rschema rest
                     pure ((l, r), rest')

parseBySchema : (schema : Schema) -> String -> Maybe (SchemaType schema)
parseBySchema schema input = case parsePrefix schema input of
     Just (res, "") => Just res
     Just _ => Nothing
     Nothing => Nothing

parseCommand : (schema: Schema) -> String -> String -> Maybe (Command schema)
parseCommand schema "add" str = do
             item <- parseBySchema schema str
             pure (Add item)
parseCommand schema "get" val = case all isDigit (unpack val) of
                              False => Nothing
                              True => Just(Get (cast val))
parseCommand schema "quit" "" = Just(Quit)
parseCommand schema "size" "" = Just(Size)
parseCommand schema "search" str = Just(Search str)
parseCommand schema "schema" str = do
             newschema <- parseSchema (words str)
             pure (SetSchema newschema)
parseCommand _ _ _ = Nothing

parse : (schema: Schema) -> (input : String) -> Maybe (Command schema)
parse schema input = case span (/= ' ') input of
                          (a, b) => parseCommand schema a (ltrim b)

display: SchemaType schema -> String
display {schema = SString} item = show item
display {schema = SInt} item = show item
display {schema = (y .+. z)} (a, b) = (display a) ++ ", " ++ (display b)

getEntry : (i : Integer) -> (store : DataStore) -> Maybe (String, DataStore)
getEntry i store = case integerToFin i (size store) of
                                          Nothing => Just("Out of range\n", store)
                                          Just id => Just(display (index id (items store)) ++ "\n", store)

zipWithIndex: Vect n a -> Vect n (Integer, a)
zipWithIndex xs = zipHelper 0 xs
             where
              zipHelper: Integer -> Vect m a -> Vect m (Integer, a)
              zipHelper i [] = []
              zipHelper i (y :: xs) = (i, y) :: zipHelper (i+1) xs


searchStore : (str : String) -> (store : DataStore) -> Maybe (String, DataStore)
searchStore str store = Just(foldl (++) "" found, store)
            where
              searchItem : (Integer, String) -> Maybe String
              searchItem (i, item) = case isInfixOf str item of
                                         False => Nothing
                                         True => Just((show i) ++ ": " ++ item ++ "\n")

              found : List String
              found = catMaybes . toList . (map searchItem) . zipWithIndex  . (map display) $ items store

setSchema : (store : DataStore) -> Schema -> Maybe DataStore
setSchema store schema = case size store of
          Z => Just (MkData schema _ [])
          S k => Nothing

process : DataStore -> String -> Maybe (String, DataStore)
process store inp = case parse (schema store) inp of
                   Nothing => Just("Invalid command\n", store)
                   Just (Add item) => Just("ID " ++ show (size store) ++ "\n", addToStore store item)
                   Just (Get i) => getEntry i store
                   Just Quit => Nothing
                   Just Size => Just("Size " ++ show (size store) ++ "\n", store)
                   Just (Search str) => searchStore str store
                   Just (SetSchema newschema) => case setSchema store newschema of
                                                       Nothing => Just("Can't update schema\n", store)
                                                       Just store' => Just("OK\n", store')


main : IO ()
main = replWith (MkData SString _ []) "Command: " process
