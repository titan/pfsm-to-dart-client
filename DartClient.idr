module DartClient

import Data.Maybe
import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser

indentDelta : Nat
indentDelta = 2

record AppConfig where
  constructor MkAppConfig
  src : String
  model : Bool
  library : Bool
  participant : String

Show AppConfig where
  show (MkAppConfig src model library participant)
    = List.join "\n" [ "src: " ++ src
                     , "model: " ++ (show model)
                     , "library: " ++ (show library)
                     , "participant: " ++ participant
                     ]

dartKeywords : List String
dartKeywords = [ "abstract"
               , "as"
               , "assert"
               , "async"
               , "await"
               , "break"
               , "case"
               , "catch"
               , "class"
               , "const"
               , "continue"
               , "covarient"
               , "default"
               , "deffered"
               , "do"
               , "dynamic"
               , "else"
               , "enum"
               , "export"
               , "extends"
               , "extension"
               , "external"
               , "factory"
               , "false"
               , "final"
               , "finally"
               , "for"
               , "Function"
               , "get"
               , "hide"
               , "if"
               , "implements"
               , "import"
               , "in"
               , "interface"
               , "is"
               , "library"
               , "mixin"
               , "new"
               , "null"
               , "on"
               , "operator"
               , "part"
               , "rethrow"
               , "return"
               , "set"
               , "show"
               , "static"
               , "super"
               , "switch"
               , "sync"
               , "this"
               , "throw"
               , "true"
               , "try"
               , "typedef"
               , "var"
               , "void"
               , "while"
               , "with"
               , "yield"
               ]

primToDartType : PrimType -> String
primToDartType PTBool   = "bool"
primToDartType PTByte   = "int"
primToDartType PTChar   = "int"
primToDartType PTShort  = "int"
primToDartType PTUShort = "int"
primToDartType PTInt    = "int"
primToDartType PTUInt   = "int"
primToDartType PTLong   = "int"
primToDartType PTULong  = "int"
primToDartType PTReal   = "double"
primToDartType PTString = "String"

toDartName : Name -> String
toDartName n
  = let n' = normalize n in
        if elemBy (==) n' dartKeywords
           then "my" ++ (capital n')
           else n'
  where
    mappings : List (String, String)
    mappings = [ (" ", "-")
               , ("+", "plus")
               ]

    normalize : Name -> String
    normalize n = let (pre :: post) = split (== '-') $ foldl (\acc, x => replaceAll (fst x) (snd x) acc) n mappings in
                      List.join "" [ pre
                                   , List.join "" $ map capital post
                                   ]

toDartType : Tipe -> String
toDartType TUnit                                 = "void"
toDartType (TPrimType t)                         = primToDartType t
toDartType (TList t)                             = "List<" ++ (toDartType t) ++ ">"
toDartType (TDict PTString (TPrimType PTString)) = "Map<String, String>"
toDartType (TDict k v)                           = "Map<" ++ (primToDartType k) ++ ", " ++ (toDartType v) ++ ">"
toDartType (TRecord n _)                         = camelize n
toDartType (TArrow _ _)                          = "Function"

toDartJson : Name -> Tipe -> String
toDartJson n TUnit         = "void"
toDartJson n (TPrimType _) = n
toDartJson n (TList _)     = n ++ ".map((i) => i.toJson()).toList()"
toDartJson n (TDict _ _)   = n ++ ".toJson()"
toDartJson n (TRecord _ _) = n ++ ".toJson()"
toDartJson n (TArrow _ _)  = n ++ ".toJson()"

fromJson : String -> Tipe -> String
fromJson src (TList t)     = src ++ ".map((i) => " ++ (fromJson "i" t) ++ ").toList()"
fromJson src (TRecord n _) = "get" ++ (camelize n) ++ "FromJson(" ++ src ++ ")"
fromJson src _             = src

toDart : AppConfig -> Fsm -> IO ()
toDart conf fsm
  = let name = fsm.name
        pre = (camelize . toDartName) name in
        if conf.model
           then putStrLn $ generateModel pre name fsm
           else putStrLn $ generateClient pre name conf.participant fsm
  where
    generateModel : String -> String -> Fsm -> String
    generateModel pre name fsm
      = let refs = liftReferences fsm.model
            rks = liftRecords fsm.model in
            join "\n\n" $ List.filter nonblank [ List.join "\n" $ map (\x => "import '../" ++ x ++ "/model.dart';") refs
                                               , join "\n\n" $ List.filter nonblank $ map (\x =>
                                                                                        case x of
                                                                                             (TRecord n ps) => generateClass (camelize n) (("fsmid", (TPrimType PTULong), Nothing):: ps)
                                                                                             _ => "") rks
                                               , generateClass pre (("fsmid", (TPrimType PTULong), Nothing) :: fsm.model)
                                               ]
      where
        generateParameter : Nat -> Parameter -> String
        generateParameter idt (n, t, ms)
          = case lookup "reference" ms of
                 Just (MVString ref) => (indent idt) ++ "final " ++ (camelize ref) ++ " " ++ (toDartName n) ++ ";"
                 _ => (indent idt) ++ "final " ++ (toDartType t) ++ " " ++ (toDartName n) ++ ";"

        generateClass : Name -> List Parameter -> String
        generateClass pre params
          = List.join "\n" [ "class " ++ pre ++ " {"
                           , List.join "\n" $ map (generateParameter indentDelta) params
                           , (indent indentDelta) ++ "const " ++ pre ++ "(" ++ (List.join ", " $ map (\(n, _, _) => "this." ++ (toDartName n)) params) ++ ");"
                           , generateToJson indentDelta params
                           , "}"
                           ]
          where
            generateToJson : Nat -> List Parameter -> String
            generateToJson idt params
              = List.join "\n" [ (indent idt) ++ "Map<String, dynamic> toJson() {"
                               , (indent (idt + indentDelta)) ++ "return {"
                               , List.join "\n" $ map (\(n, t, ms) =>
                                                    case lookup "reference" ms of
                                                         Just (MVString ref) => (indent (idt + (indentDelta * 2))) ++ "'" ++ n ++ "': " ++ n ++ ".toJson(),"
                                                         _ => (indent (idt + (indentDelta * 2))) ++ "'" ++ n ++ "': " ++ (toDartJson n t) ++ ",") params
                               , (indent (idt + indentDelta)) ++ "};"
                               , (indent idt) ++ "}"
                               ]

    generateClient : String -> String -> String -> Fsm -> String
    generateClient pre name participant fsm
      = let refs = liftReferences fsm.model
            rks = liftRecords fsm.model
            events = liftEventsByParticipantFromTransitions participant fsm.transitions in
            join "\n\n" $ List.filter nonblank [ generateImports refs
                                               , generateRecordsFromJson pre name rks
                                               , generateFromJson pre name fsm.model
                                               , generateFetchLists pre name fsm.model fsm.states
                                               , generateEvents pre name events
                                               ]
      where
        liftEventsByParticipantFromTriggers : String -> List1 Trigger -> List Event
        liftEventsByParticipantFromTriggers participant triggers
          = foldl (\acc, (MkTrigger ps evt _ _) =>
              if elemBy (==) participant $ map (\(MkParticipant n _) => n) ps
                 then evt :: acc
                 else acc) [] triggers

        liftEventsByParticipantFromTransitions : String -> List1 Transition -> List Event
        liftEventsByParticipantFromTransitions participant transitions
          = foldl (\acc, x => acc ++ (liftEventsByParticipantFromTriggers participant x.triggers)) [] transitions

        generateImports : List String -> String
        generateImports refs
          = List.join "\n" [ "import 'dart:convert';"
                           , "import 'package:crypto/crypto.dart';"
                           , "import 'package:http/http.dart' as http;"
                           , "import 'package:intl/intl.dart';"
                           , "import '../api-helper.dart';"
                           , "import 'model.dart';"
                           , List.join "\n" $ map (\x => "import '../" ++ x ++ "/model.dart';") refs
                           , List.join "\n" $ map (\x => "import '../" ++ x ++ "/api.dart';") refs
                           ]

        generateFromJson : String -> String -> List Parameter -> String
        generateFromJson pre name model
          = List.join "\n" [ pre ++ " get" ++ pre ++ "FromJson(Map<String, dynamic> node) {"
                           , (indent indentDelta) ++ "var fsmid = int.parse(node['fsmid']);"
                           , List.join "\n" $ map (generateParsingFromJson indentDelta) model
                           , (indent indentDelta) ++ "var " ++ (toDartName name) ++ " = " ++ pre ++ "(" ++ (List.join ", " $ map generateInitialingObject (("fsmid", (TPrimType PTString) , Nothing) :: model)) ++ ");"
                           , (indent indentDelta) ++ "return " ++ (toDartName name) ++ ";"
                           , "}"
                           ]
          where
            generateParsingFromJson : Nat -> Parameter -> String
            generateParsingFromJson idt (n, t, ms)
              = case lookup "reference" ms of
                     Just (MVString ref) => (indent idt) ++ "var " ++ (toDartName n) ++ " = " ++ "get" ++ (camelize ref) ++ "FromJson(node['" ++ n ++ "']);"
                     _ => (indent idt) ++ "var " ++ (toDartName n) ++ " = " ++ (fromJson ("node['" ++ n ++ "']") t) ++ ";"

            generateInitialingObject : Parameter -> String
            generateInitialingObject (n, _, _)
              = (toDartName n)

        generateRecordsFromJson : String -> String -> List Tipe -> String
        generateRecordsFromJson pre name rks
          = List.join "\n\n" $ map (generateRecordFromJson pre name) rks
          where
            generateRecordFromJson : String -> String -> Tipe -> String
            generateRecordFromJson pre name (TRecord n ps)
              = List.join "\n" [ (camelize n) ++ " get" ++ (camelize n) ++ "FromJson(Map<String, dynamic> node) {"
                               , List.join "\n" $ map (generateParsingFromJson indentDelta) ps
                               , (indent indentDelta) ++ "var " ++ (toDartName n) ++ " = " ++ pre ++ "(" ++ (List.join ", " $ map generateInitialingObject ps) ++ ");"
                               , (indent indentDelta) ++ "return " ++ (toDartName n) ++ ";"
                               , "}"
                               ]
              where
                generateParsingFromJson : Nat -> Parameter -> String
                generateParsingFromJson idt (n, t, ms)
                  = case lookup "reference" ms of
                         Just (MVString ref) => (indent idt) ++ "var " ++ (toDartName n) ++ " = " ++ "get" ++ (camelize ref) ++ "FromJson(node['" ++ n ++ "']);"
                         _ => (indent idt) ++ "var " ++ (toDartName n) ++ " = " ++ "node['" ++ n ++ "'];"

                generateInitialingObject : Parameter -> String
                generateInitialingObject (n, _, _)
                  = (toDartName n)

            generateRecordFromJson pre name _ = ""

        generateFetchLists : String -> String -> List Parameter -> List1 State -> String
        generateFetchLists pre name model states
          = List1.join "\n\n" $ map (generateFetchList pre name model) states
          where
            generateFetchList : String -> String -> List Parameter -> State -> String
            generateFetchList pre name model (MkState sname _ _ _)
              = let path = "/" ++ name ++ "/" ++ sname
                    query = "limit=${limit}&offset=${offset}" in
                    List.join "\n" [ "Future<Pagination<" ++ pre ++ ">> " ++ "get" ++ (camelize (sname ++ "-"  ++ name ++ "-list")) ++ "(Caller self, {int offset = 0, int limit = 10}) async {"
                                   , (indent (indentDelta * 1)) ++ "var signbody = '" ++ query ++ "';"
                                   , (indent (indentDelta * 1)) ++ "var now = DateTime.now().toUtc();"
                                   , (indent (indentDelta * 1)) ++ "var formatter = DateFormat('EEE, dd MMM yyyy HH:mm:ss');"
                                   , (indent (indentDelta * 1)) ++ "var date = formatter.format(now) + ' GMT';"
                                   , (indent (indentDelta * 1)) ++ "var hmacSha256 = Hmac(sha256, utf8.encode(self.appkey));"
                                   , (indent (indentDelta * 1)) ++ "var secretValue = hmacSha256.convert(utf8.encode('GET|" ++ path ++ "|${signbody}|${date}'));"
                                   , (indent (indentDelta * 1)) ++ "var headers = {"
                                   , (indent (indentDelta * 2)) ++ "'Date': date,"
                                   , (indent (indentDelta * 2)) ++ "'Authorization': '${self.appid}:${secretValue}',"
                                   , (indent (indentDelta * 2)) ++ "'x-noise': self.rand.nextInt(0xFFFFFFFF).toRadixString(16),"
                                   , (indent (indentDelta * 2)) ++ "'x-token': self.accessToken,"
                                   , (indent (indentDelta * 1)) ++ "};"
                                   , (indent (indentDelta * 1)) ++ "var response = await http.get('${self.schema}://${self.host}:${self.port}" ++ path ++ "?" ++ query ++ "', headers: headers);"
                                   , (indent (indentDelta * 1)) ++ "if (response.statusCode == 200) {"
                                   , (indent (indentDelta * 2)) ++ "var respbody = jsonDecode(response.body);"
                                   , (indent (indentDelta * 2)) ++ "final int code = respbody['code'];"
                                   , (indent (indentDelta * 2)) ++ "var payload = respbody['payload'];"
                                   , (indent (indentDelta * 2)) ++ "if (code == 200) {"
                                   , (indent (indentDelta * 3)) ++ "var data = [];"
                                   , (indent (indentDelta * 3)) ++ "for (var e in payload['data']) {"
                                   , (indent (indentDelta * 4)) ++ "var " ++ (toDartName name) ++ " = get" ++ pre ++ "FromJson(e);"
                                   , (indent (indentDelta * 4)) ++ "data.add(" ++ (toDartName name) ++ ");"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 3)) ++ "var pagination = payload['pagination'];"
                                   , (indent (indentDelta * 3)) ++ "return Pagination<" ++ pre ++ ">(data.cast<" ++ pre ++ ">(), pagination['offset'], pagination['limit']);"
                                   , (indent (indentDelta * 2)) ++ "} else {"
                                   , (indent (indentDelta * 3)) ++ "throw ApiException(code, payload);"
                                   , (indent (indentDelta * 2)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "} else {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(response.statusCode, response.body);"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , "}"
                                   ]

        generateEvents : String -> String -> List Event -> String
        generateEvents pre name evts
          = join "\n\n" $ map (generateEvent pre name) evts
          where
            generateEvent : String -> String -> Event -> String
            generateEvent pre name (MkEvent ename params metas)
              = let isCreator = (MVString "true") == (fromMaybe (MVString "false") $ lookup "creator" metas)
                    returnType = if isCreator then "int" else "bool"
                    path = if isCreator then ("/" ++ name ++ "/" ++ ename) else ("/" ++ name ++ "/${fsmid}/" ++ ename)
                    params' = if isCreator then params else (("fsmid", (TPrimType PTULong) , Nothing) :: (the (List Parameter) params)) in
                    List.join "\n" [ "Future<" ++ returnType ++ "> " ++ (toDartName ename) ++ "(Caller self, " ++ (generateParametersSignature params') ++ ") async {"
                                   , (indent (indentDelta * 1)) ++ "var body = json.encode({" ++ (List.join ", " (map (\(n, t, _) => "'" ++ n ++ "': " ++ (toDartJson n t)) params)) ++ "});"
                                   , (indent (indentDelta * 1)) ++ "var signbody = '" ++ (List.join "&" $ map generateSignatureBody $ sortBy (\(a, _, _), (b, _, _) => compare a b) params) ++ "';"
                                   , (indent (indentDelta * 1)) ++ "var now = DateTime.now().toUtc();"
                                   , (indent (indentDelta * 1)) ++ "var formatter = DateFormat('EEE, dd MMM yyyy HH:mm:ss');"
                                   , (indent (indentDelta * 1)) ++ "var date = formatter.format(now) + ' GMT';"
                                   , (indent (indentDelta * 1)) ++ "var hmacSha256 = Hmac(sha256, utf8.encode(self.appkey));"
                                   , (indent (indentDelta * 1)) ++ "var secretValue = hmacSha256.convert(utf8.encode('POST|" ++ path ++ "|${signbody}|${date}'));"
                                   , (indent (indentDelta * 1)) ++ "var headers = {"
                                   , (indent (indentDelta * 2)) ++ "'Date': date,"
                                   , (indent (indentDelta * 2)) ++ "'Authorization': '${self.appid}:${secretValue}',"
                                   , (indent (indentDelta * 2)) ++ "'x-noise': self.rand.nextInt(0xFFFFFFFF).toRadixString(16),"
                                   , (indent (indentDelta * 2)) ++ "'x-token': self.accessToken,"
                                   , (indent (indentDelta * 1)) ++ "};"
                                   , (indent (indentDelta * 1)) ++ "var response = await http.post('${self.schema}://${self.host}:${self.port}" ++ path ++ "', headers: headers, body: body);"
                                   , (indent (indentDelta * 1)) ++ "if (response.statusCode == 200) {"
                                   , (indent (indentDelta * 2)) ++ "var respbody = jsonDecode(response.body);"
                                   , (indent (indentDelta * 2)) ++ "final int code = respbody['code'];"
                                   , (indent (indentDelta * 2)) ++ "if (code == 200) {"
                                   , (indent (indentDelta * 3)) ++ (if isCreator then "return respbody['payload'];" else "return respbody['payload'] == 'Okay';")
                                   , (indent (indentDelta * 2)) ++ "} else {"
                                   , (indent (indentDelta * 3)) ++ "throw ApiException(code, respbody['payload']);"
                                   , (indent (indentDelta * 2)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "} else {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(response.statusCode, response.body);"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , "}"
                                   ]
              where
                generateParametersSignature : List Parameter -> String
                generateParametersSignature ps
                  = List.join ", " $ map (\(n, t, _) => (toDartType t) ++ " " ++ (toDartName n)) ps

                generateSignatureBody : Parameter -> String
                generateSignatureBody (n, (TList _), _)   = n ++ "=${json.encode(" ++ (toDartName n) ++ ".map((i) => i.toJson()).toList())}"
                generateSignatureBody (n, (TDict _ _), _) = n ++ "=${json.encode(" ++ (toDartName n) ++ ")}"
                generateSignatureBody (n, _,           _) = n ++ "=$" ++ (toDartName n)

generateLibrary : String
generateLibrary
  = join "\n\n" $ List.filter nonblank [ "import 'dart:math';"
                                       , generatePagination
                                       , generateCaller
                                       , generateApiException
                                       ]
  where
    generatePagination : String
    generatePagination
      = List.join "\n" [ "class Pagination<T> {"
                       , (indent indentDelta) ++ "final List<T> data;"
                       , (indent indentDelta) ++ "final int offset;"
                       , (indent indentDelta) ++ "final int limit;"
                       , (indent indentDelta) ++ "const Pagination(this.data, this.offset, this.limit);"
                       , "}"
                       ]

    generateCaller : String
    generateCaller
      = List.join "\n" [ "class Caller {"
                       , (indent indentDelta) ++ "final String schema;"
                       , (indent indentDelta) ++ "final String host;"
                       , (indent indentDelta) ++ "final int port;"
                       , (indent indentDelta) ++ "final String appid;"
                       , (indent indentDelta) ++ "final String appkey;"
                       , (indent indentDelta) ++ "final Random rand;"
                       , (indent indentDelta) ++ "String accessToken;"
                       , (indent indentDelta) ++ "String refreshToken;"
                       , (indent indentDelta) ++ "Caller(this.schema, this.host, this.port, this.appid, this.appkey, this.rand);"
                       , "}"
                       ]

    generateApiException : String
    generateApiException
      = List.join "\n" [ "class ApiException implements Exception {"
                       , (indent indentDelta) ++ "final int code;"
                       , (indent indentDelta) ++ "final String error;"
                       , (indent indentDelta) ++ "const ApiException(this.code, this.error);"
                       , "}"
                       ]

doWork : AppConfig -> IO ()
doWork conf
  = if conf.library
       then putStrLn $ generateLibrary
       else do Right fsm <- loadFsmFromFile conf.src
               | Left err => putStrLn err
               toDart conf fsm

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing False False Nothing
  where
    parseArgs' : Maybe String -> Bool -> Bool -> Maybe String -> List String -> Maybe AppConfig
    parseArgs' _          _     True    _                  []                  = Just (MkAppConfig "" False True "")
    parseArgs' Nothing    _     False   _                  []                  = Nothing
    parseArgs' (Just src) True  _       Nothing            []                  = Just (MkAppConfig src True False "")
    parseArgs' (Just _)   False _       Nothing            []                  = Nothing
    parseArgs' (Just src) model library (Just participant) []                  = Just (MkAppConfig src model library participant)
    parseArgs' src        _     library participant        ("--model" :: xs)   = parseArgs' src True library participant xs
    parseArgs' src        model _       participant        ("--library" :: xs) = parseArgs' src model True participant xs
    parseArgs' src        model library _                  ("-p" :: x :: xs)   = parseArgs' src model library (Just x) xs
    parseArgs' _          model library participant        (x :: xs)           = parseArgs' (Just x) model library participant xs

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-dart-client [options] <src>"
                   , ""
                   , "Options:"
                   , "  --model         Just generate data model.[default: false]."
                   , "  --library       Just generate code of supporting library.[default: false]."
                   , "  -p <particpant> Specify the participant to call APIs."
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
