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
import Pfsm.Service2

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
dartClientKeywords : List String
dartClientKeywords = [ "http"
                     , "session"
                     , "signbody"
                     , "utf8"
                     ]

primToDartType : PrimType -> String
primToDartType PTBool   = "bool"
primToDartType PTByte   = "int"
primToDartType PTChar   = "int"
primToDartType PTShort  = "int"
primToDartType PTUShort = "int"
primToDartType PTInt    = "int"
primToDartType PTUInt   = "int"
primToDartType PTLong   = "BigInt"
primToDartType PTULong  = "BigInt"
primToDartType PTReal   = "double"
primToDartType PTString = "String"

toDartName : Name -> String
toDartName n
  = let n' = normalize n in
        if elemBy (==) n' (dartKeywords ++ dartClientKeywords)
           then "my" ++ (capital n')
           else n'
  where
    mappings : List (String, String)
    mappings
      = [ (" ", "-")
        , ("+", "plus")
        ]

    normalize : Name -> String
    normalize n
      = let (pre :: post) = split (== '-') $ foldl (\acc, x => replaceAll (fst x) (snd x) acc) n mappings in
            List.join "" [ pre
                         , List.join "" $ map capital post
                         ]

toDartType : Tipe -> String
toDartType TUnit         = "void"
toDartType (TPrimType t) = primToDartType t
toDartType (TList t)     = "List<" ++ (toDartType t) ++ ">"
toDartType (TDict k v)   = "Map<" ++ (primToDartType k) ++ ", " ++ (toDartType v) ++ ">"
toDartType (TRecord n _) = camelize n
toDartType (TArrow _ _)  = "Function"

toDartJson : Name -> Tipe -> String
toDartJson n TUnit                       = "void"
toDartJson n (TPrimType PTLong)          = (toDartName n) ++ ".toString()"
toDartJson n (TPrimType PTULong)         = (toDartName n) ++ ".toString()"
toDartJson n (TPrimType _)               = (toDartName n)
toDartJson n (TList (TPrimType PTULong)) = (toDartName n) ++ ".map((i) => i.toString()).toList()"
toDartJson n (TList (TPrimType PTLong))  = (toDartName n) ++ ".map((i) => i.toString()).toList()"
toDartJson n (TList (TPrimType _))       = (toDartName n)
toDartJson n (TList _)                   = (toDartName n) ++ ".map((i) => i.toJson()).toList()"
toDartJson n (TDict _ _)                 = (toDartName n)
toDartJson n (TRecord _ _)               = (toDartName n) ++ ".toJson()"
toDartJson n (TArrow _ _)                = (toDartName n) ++ ".toJson()"

fromJson : String -> Tipe -> String
fromJson src t
  = fromJson' src t Z
  where
    fromJson' : String -> Tipe -> Nat -> String
    fromJson' src (TList t)           dep = "List<" ++ (toDartType t) ++ ">.from(" ++ src ++ ".map((i" ++ (show dep) ++ ") => " ++ (fromJson' ("i" ++ (show dep)) t (S dep)) ++ "))"
    fromJson' src (TDict k v)         dep = src ++ ".map<" ++ (primToDartType k) ++ ", " ++ (toDartType v) ++ ">((k" ++ (show dep) ++ ", v" ++ (show dep) ++ ") => MapEntry<" ++ (primToDartType k) ++ ", " ++ (toDartType v) ++ ">(" ++ (fromJson' ("k" ++ show dep) (TPrimType k) (S dep)) ++ ", " ++ (fromJson' ("v" ++ show dep) v (S dep)) ++ "))"
    fromJson' src (TRecord n _)       _   = "get" ++ (camelize n) ++ "FromJson(" ++ src ++ ")"
    fromJson' src (TPrimType PTLong)  _   = "BigInt.parse(" ++ src ++ ")"
    fromJson' src (TPrimType PTULong) _   = "BigInt.parse(" ++ src ++ ")"
    fromJson' src _                   _   = src

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
                                                                                             (TRecord n ps) => generateClass (camelize n) ps
                                                                                             _ => "") rks
                                               , generateClass pre (("fsmid", (TPrimType PTULong), Nothing) :: fsm.model)
                                               ]
      where
        generateParameter : Nat -> Parameter -> String
        generateParameter idt (n, (TList (TPrimType PTLong)), ms)
          = case lookup "reference" ms of
                 Just (MVString ref) => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                                       , (indent idt) ++ "final List<BigInt> " ++ (toDartName n) ++ ";"
                                                       ,  (indent idt) ++ "/// " ++ (displayName n ms) ++ "对象"
                                                       , (indent idt) ++ "final List<" ++ (camelize $ toDartName ref) ++ "> " ++ (toDartName (n ++ "-refs")) ++ ";"
                                                       ]
                 _ => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                     , (indent idt) ++ "final List<BigInt> " ++ (toDartName n) ++ ";"
                                     ]
        generateParameter idt (n, (TList (TPrimType PTULong)), ms)
          = case lookup "reference" ms of
                 Just (MVString ref) => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                                       , (indent idt) ++ "final List<BigInt> " ++ (toDartName n) ++ ";"
                                                       ,  (indent idt) ++ "/// " ++ (displayName n ms) ++ "对象"
                                                       , (indent idt) ++ "final List<" ++ (camelize $ toDartName ref) ++ "> " ++ (toDartName (n ++ "-refs")) ++ ";"
                                                       ]
                 _ => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                     , (indent idt) ++ "final List<BigInt> " ++ (toDartName n) ++ ";"
                                     ]
        generateParameter idt (n, t, ms)
          = case lookup "reference" ms of
                 Just (MVString ref) => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                                       , (indent idt) ++ "final BigInt " ++ (toDartName n) ++ ";"
                                                       ,  (indent idt) ++ "/// " ++ (displayName n ms) ++ "对象"
                                                       , (indent idt) ++ "final " ++ (camelize $ toDartName ref) ++ " " ++ (toDartName (n ++ "-ref")) ++ ";"
                                                       ]
                 _ => List.join "\n" [ (indent idt) ++ "/// " ++ (displayName n ms)
                                     , (indent idt) ++ "final " ++ (toDartType t) ++ " " ++ (toDartName n) ++ ";"
                                     ]

        generateClass : Name -> List Parameter -> String
        generateClass pre params
          = List.join "\n" [ "class " ++ pre ++ " {"
                           , List.join "\n" $ map (generateParameter indentDelta) params
                           , (indent indentDelta) ++ "const " ++ pre ++ "(" ++ (List.join ", " $ map generateConstructorParameter params) ++ ");"
                           , generateToJson indentDelta params
                           , "}"
                           ]
          where
            generateConstructorParameter : Parameter -> String
            generateConstructorParameter (n, (TList _), metas)
              = case lookup "reference" metas of
                     Just (MVString _) => List.join ", " [ "this." ++ (toDartName n)
                                                         , "this." ++ (toDartName (n ++ "-refs"))
                                                         ]
                     _ => "this." ++ (toDartName n)
            generateConstructorParameter (n, _, metas)
              = case lookup "reference" metas of
                     Just (MVString _) => List.join ", " [ "this." ++ (toDartName n)
                                                         , "this." ++ (toDartName (n ++ "-ref"))
                                                         ]
                     _ => "this." ++ (toDartName n)

            generateAttributeToJson : Nat -> Parameter -> String
            generateAttributeToJson idt (n, t, metas)
              = (indent idt) ++ "'" ++ n ++ "': " ++ (toDartJson n t) ++ ","

            generateToJson : Nat -> List Parameter -> String
            generateToJson idt params
              = List.join "\n" [ (indent idt) ++ "Map<String, dynamic> toJson() {"
                               , (indent (idt + indentDelta)) ++ "return {"
                               , List.join "\n" $ map (generateAttributeToJson (idt + indentDelta * 2)) params
                               , (indent (idt + indentDelta)) ++ "};"
                               , (indent idt) ++ "}"
                               ]

    generateClient : String -> String -> String -> Fsm -> String
    generateClient pre name participant fsm
      = let refs = liftReferences fsm.model
            rks = liftRecords fsm.model
            manyToOneFields = filter manyToOneFieldFilter fsm.model
            searchable = isSearchable fsm.metas
            events = liftEventsByParticipantFromTransitions participant fsm.transitions
            participated = length (filter (\(MkParticipant pname _) => pname == participant) fsm.participants) /= 0 in
            join "\n\n" $ List.filter nonblank [ generateImports refs
                                               , generateRecordsFromJson pre name rks
                                               , generateFromJson pre name fsm.model
                                               , if participated
                                                    then generateFetchObject pre name fsm
                                                    else ""
                                               , if participated
                                                    then generateFetchLists pre name participant fsm.states fsm.transitions
                                                    else ""
                                               , if participated
                                                    then generateFetchListsByReferences pre name participant fsm.states fsm.transitions manyToOneFields
                                                    else ""
                                               , if participated && searchable
                                                    then generateStateSearchs pre name participant fsm.states fsm.transitions
                                                    else ""
                                               , if participated
                                                    then generateEvents pre name events
                                                    else ""
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
          = nub $ foldl (\acc, x => acc ++ (liftEventsByParticipantFromTriggers participant x.triggers)) [] transitions

        generateParametersSignature : List Parameter -> String
        generateParametersSignature ps
          = List.join ", " $ map (\(n, t, _) => (toDartType t) ++ " " ++ (toDartName n)) ps

        generateImports : List String -> String
        generateImports refs
          = List.join "\n" [ "import 'dart:convert';"
                           , "import 'dart:io';"
                           , "import 'package:crypto/crypto.dart';"
                           , "import 'package:http/http.dart' as http;"
                           , "import 'package:intl/intl.dart';"
                           , "import '../api-helper.dart';"
                           , "import '../session/api.dart' as session;"
                           , "import 'model.dart';"
                           , List.join "\n" $ map (\x => "import '../" ++ x ++ "/model.dart';") refs
                           , List.join "\n" $ map (\x => "import '../" ++ x ++ "/api.dart';") refs
                           ]

        generateFromJson : String -> String -> List Parameter -> String
        generateFromJson pre name model
          = List.join "\n" [ pre ++ " get" ++ pre ++ "FromJson(Map<String, dynamic> node) {"
                           , (indent indentDelta) ++ "final fsmid = BigInt.parse(node['fsmid']);"
                           , List.join "\n" $ map (generateParsingFromJson indentDelta) model
                           , (indent indentDelta) ++ "final " ++ (toDartName name) ++ " = " ++ pre ++ "(" ++ (List.join ", " $ map generateInitialingObject (("fsmid", (TPrimType PTString) , Nothing) :: model)) ++ ");"
                           , (indent indentDelta) ++ "return " ++ (toDartName name) ++ ";"
                           , "}"
                           ]
          where
            generateParsingFromJson : Nat -> Parameter -> String
            generateParsingFromJson idt (n, (TList t), ms)
              = case lookup "reference" ms of
                     Just (MVString ref) => List.join "\n" [ (indent idt) ++ "final " ++ (toDartName n) ++ " = List<BigInt>.from(node['" ++ n ++ "'].where((i) => i != '0').map((i) => " ++ (fromJson "i['fsmid']" t) ++ "));"
                                                           , (indent idt) ++ "final " ++ (toDartName (n ++ "-refs")) ++ " = List<" ++ (camelize ref) ++ ">.from(node['" ++ n ++ "'].where((i) => i != '0').map((i) => " ++ (toDartName ("get-" ++ (camelize $ toDartName ref) ++ "-from-json")) ++ "(i)));"
                                                           ]
                     _ => (indent idt) ++ "final " ++ (toDartName n) ++ " = " ++ (fromJson ("node['" ++ n ++ "']") (TList t)) ++ ";"
            generateParsingFromJson idt (n, t, ms)
              = case lookup "reference" ms of
                     Just (MVString ref) => List.join "\n" [ (indent idt) ++ "final " ++ (toDartName n) ++ " = node['" ++ n ++ "'] == '0'? BigInt.zero: " ++ (fromJson ("node['" ++ n ++ "']['fsmid']") t) ++ ";"
                                                           , (indent idt) ++ "final " ++ (toDartName (n ++ "-ref")) ++ " = node['" ++ n ++ "'] == '0'? null: " ++ (toDartName ("get-" ++ (camelize $ toDartName ref) ++ "-from-json")) ++ "(node['" ++ n ++ "']);"
                                                           ]
                     _ => (indent idt) ++ "final " ++ (toDartName n) ++ " = " ++ (fromJson ("node['" ++ n ++ "']") t) ++ ";"

            generateInitialingObject : Parameter -> String
            generateInitialingObject (n, (TList _), ms)
              = case lookup "reference" ms of
                     Just (MVString ref) => List.join ", " [ (toDartName n)
                                                           , (toDartName (n ++ "-refs"))
                                                           ]
                     _ => toDartName n
            generateInitialingObject (n, _, ms)
              = case lookup "reference" ms of
                     Just (MVString ref) => List.join ", " [ (toDartName n)
                                                           , (toDartName (n ++ "-ref"))
                                                           ]
                     _ => toDartName n

        generateRecordsFromJson : String -> String -> List Tipe -> String
        generateRecordsFromJson pre name rks
          = List.join "\n\n" $ map (generateRecordFromJson pre name) rks
          where
            generateRecordFromJson : String -> String -> Tipe -> String
            generateRecordFromJson pre name (TRecord n ps)
              = List.join "\n" [ (camelize n) ++ " " ++ (toDartName ("get-" ++ n ++ "-from-json")) ++ "(Map<String, dynamic> node) {"
                               , List.join "\n" $ map (generateParsingFromJson indentDelta) ps
                               , (indent indentDelta) ++ "final " ++ (toDartName n) ++ " = " ++ (camelize n) ++ "(" ++ (List.join ", " $ map generateInitialingObject ps) ++ ");"
                               , (indent indentDelta) ++ "return " ++ (toDartName n) ++ ";"
                               , "}"
                               ]
              where
                generateParsingFromJson : Nat -> Parameter -> String
                generateParsingFromJson idt (n, (TList t), ms)
                  = case lookup "reference" ms of
                         Just (MVString ref) => List.join "\n" [ (indent idt) ++ "final " ++ (toDartName n) ++ " = node['" ++ n ++ "'].where((i) => i != '0').map((i) => " ++ (fromJson "i['fsmid']" t) ++ ").toList();"
                                                               , (indent idt) ++ "final " ++ (toDartName (n ++ "-refs")) ++ " = (node['" ++ n ++ "']).where((i) => i != '0').map((i) => " ++ (toDartName ("get-" ++ (camelize $ toDartName ref) ++ "-from-json")) ++ "(i)).toList();"
                                                               ]
                         _ => (indent idt) ++ "final " ++ (toDartName n) ++ " = node['" ++ n ++ "'].map((i) => " ++ (fromJson "i" t) ++ ");"
                generateParsingFromJson idt (n, t, ms)
                  = case lookup "reference" ms of
                         Just (MVString ref) => List.join "\n" [ (indent idt) ++ "final " ++ (toDartName n) ++ " = node['" ++ n ++ "'] == '0'? BigInt.zero: " ++ (fromJson ("node['" ++ n ++ "']['fsmid']") t) ++ ";"
                                                               , (indent idt) ++ "final " ++ (toDartName (n ++ "-ref")) ++ " = node['" ++ n ++ "'] == '0'? null: " ++ (toDartName ("get-" ++ (camelize $ toDartName ref) ++ "-from-json")) ++ "(node['" ++ n ++ "']);"
                                                               ]
                         _ => (indent idt) ++ "final " ++ (toDartName n) ++ " = " ++ (fromJson ("node['" ++ n ++ "']") t) ++ ";"

                generateInitialingObject : Parameter -> String
                generateInitialingObject (n, (TList _), metas)
                  = case lookup "reference" metas of
                         Just (MVString _) => List.join ", " [ (toDartName n)
                                                             , (toDartName (n ++ "-refs"))
                                                             ]
                         _ => toDartName n
                generateInitialingObject (n, _, metas)
                  = case lookup "reference" metas of
                         Just (MVString _) => List.join ", " [ (toDartName n)
                                                             , (toDartName (n ++ "-ref"))
                                                             ]
                         _ => toDartName n

            generateRecordFromJson pre name _ = ""

        generateFetchObject : String -> String -> Fsm -> String
        generateFetchObject pre name fsm
          = let fsmIdStyle = fsmIdStyleOfFsm fsm
                signpath = case fsmIdStyle of
                                FsmIdStyleSession => "/" ++ name
                                _ => "/" ++ name ++ "/${_fsmid}"
                path = "${_self.basePath}" ++ signpath
                params = case fsmIdStyle of
                              FsmIdStyleSession => ("_self", (TRecord "Caller" []), Nothing) :: ("_tokensOption", (TRecord "Tuple<String, String>" []), Nothing) :: ("_countdown", (TPrimType PTUInt), Nothing) :: []
                              _ => ("_self", (TRecord "Caller" []), Nothing) :: ("_tokensOption", (TRecord "Tuple<String, String>" []), Nothing) :: ("_countdown", (TPrimType PTUInt), Nothing) :: ("_fsmid", (TPrimType PTULong), Nothing) :: []
                params' = case fsmIdStyle of
                               FsmIdStyleSession => ("_self", (TRecord "Caller" []), Nothing) :: []
                               _ => ("_self", (TRecord "Caller" []), Nothing) :: ("_fsmid", (TPrimType PTULong), Nothing) :: []
                in
                List.join "\n" [ "Future<Tuple<Tuple<String, String>, " ++ pre ++ ">> _get" ++ pre ++ "(" ++ (generateParametersSignature params) ++ ") async {"
                               , (indent (indentDelta * 1)) ++ "if (_countdown == 0) {"
                               , (indent (indentDelta * 2)) ++ "throw ApiException(403, '会话过期');"
                               , (indent (indentDelta * 1)) ++ "}"
                               , (indent (indentDelta * 1)) ++ "final _signbody = '';"
                               , (indent (indentDelta * 1)) ++ "final _noise1 = _self.rand.nextInt(0xFFFFFFFF);"
                               , (indent (indentDelta * 1)) ++ "final _noise2 = _self.rand.nextInt(0xFFFFFFFF);"
                               , (indent (indentDelta * 1)) ++ "final _date = DateFormat('EEE, dd MMM yyyy HH:mm:ss', 'en_US').format(DateTime.now().toUtc()) + ' GMT';"
                               , (indent (indentDelta * 1)) ++ "final _secretValue = Hmac(sha256, utf8.encode(_self.appkey)).convert(utf8.encode('GET|" ++ signpath ++ "|${_signbody}|${_date}'));"
                               , (indent (indentDelta * 1)) ++ "final _headers = {"
                               , (indent (indentDelta * 2)) ++ "'x-date': _date,"
                               , (indent (indentDelta * 2)) ++ "'Authorization': '${_self.appid}:${_secretValue}',"
                               , (indent (indentDelta * 2)) ++ "'x-noise': '${_noise1.toRadixString(16)}${_noise2.toRadixString(16).padLeft(8, '0')}',"
                               , (indent (indentDelta * 2)) ++ "'x-token': _self.accessToken,"
                               , (indent (indentDelta * 1)) ++ "};"
                               , (indent (indentDelta * 1)) ++ "final _response = await http.get('${_self.schema}://${_self.host}:${_self.port}" ++ path ++ "', headers: _headers);"
                               , (indent (indentDelta * 1)) ++ "if (_response.statusCode == 200) {"
                               , (indent (indentDelta * 2)) ++ "final _respbody = jsonDecode(_response.body);"
                               , (indent (indentDelta * 2)) ++ "final int _code = _respbody['code'];"
                               , (indent (indentDelta * 2)) ++ "if (_code == 200) {"
                               , (indent (indentDelta * 3)) ++ "return Tuple<Tuple<String, String>, " ++ pre ++ ">(_tokensOption, get" ++ pre ++ "FromJson(_respbody['payload']));"
                               , (indent (indentDelta * 2)) ++ "} else if (_code == 403) {"
                               , (indent (indentDelta * 3)) ++ "try {"
                               , (indent (indentDelta * 4)) ++ "_tokensOption = await session.refresh(_self);"
                               , (indent (indentDelta * 4)) ++ "_self.accessToken = _tokensOption.a;"
                               , (indent (indentDelta * 4)) ++ "_self.refreshToken = _tokensOption.b;"
                               , (indent (indentDelta * 4)) ++ "return _get" ++ pre ++ "(" ++ (generateCallArguments params) ++ ");"
                               , (indent (indentDelta * 3)) ++ "} on ApiException {"
                               , (indent (indentDelta * 4)) ++ "await Future.delayed(const Duration(seconds:1));"
                               , (indent (indentDelta * 4)) ++ "_countdown -= 1;"
                               , (indent (indentDelta * 4)) ++ "return _get" ++ pre ++ "(" ++ (generateCallArguments params) ++ ");"
                               , (indent (indentDelta * 3)) ++ "}"
                               , (indent (indentDelta * 2)) ++ "} else {"
                               , (indent (indentDelta * 3)) ++ "throw ApiException(_code, _respbody['payload']);"
                               , (indent (indentDelta * 2)) ++ "}"
                               , (indent (indentDelta * 1)) ++ "} else {"
                               , (indent (indentDelta * 2)) ++ "throw ApiException(_response.statusCode, _response.body);"
                               , (indent (indentDelta * 1)) ++ "}"
                               , "}"
                               , ""
                               , "Future<Tuple<Tuple<String, String>, " ++ pre ++ ">> get" ++ pre ++ "(" ++ (generateParametersSignature params') ++ ") async {"
                               , (indent indentDelta) ++ "final _tokensOption = null;"
                               , (indent indentDelta) ++ "final _countdown = 2;"
                               , (indent indentDelta) ++ "return _get" ++ pre ++ "(" ++ (generateCallArguments params) ++ ");"
                               , "}"
                               ]
          where
            generateCallArguments : List Parameter -> String
            generateCallArguments params
              = List.join ", " $ map (\(n, _, _) => (toDartName n)) params

        generateFetchLists : String -> String -> String -> List1 State -> List1 Transition -> String
        generateFetchLists pre name pname states transitions
          = let filteredStates = liftListStates states transitions
                pairs = liftListStatesOfParticipants states transitions
                filteredStatesOfParticipant = map (\(s, _) => s) $ filter (\(_, p) => p == pname) pairs
                combinedStates = nubBy (\(MkState x _ _ _), (MkState y _ _ _) => x == y) (filteredStates ++ filteredStatesOfParticipant) in
                List.join "\n\n" $ map (generateFetchList pre name) combinedStates
          where
            generateFetchList : String -> String -> State -> String
            generateFetchList pre name (MkState sname _ _ _)
              = let signpath = "/" ++ name ++ "/" ++ sname
                    path = "${_self.basePath}" ++ signpath
                    query = "limit=${limit}&offset=${offset}" in
                    List.join "\n" [ "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list")) ++ "(Caller _self, Tuple<String, String> _tokensOption, int _countdown, {int offset = 0, int limit = 10}) async {"
                                   , (indent (indentDelta * 1)) ++ "if (_countdown == 0) {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(403, '会话过期');"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "final _signbody = '" ++ query ++ "';"
                                   , (indent (indentDelta * 1)) ++ "final _noise1 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _noise2 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _date = DateFormat('EEE, dd MMM yyyy HH:mm:ss', 'en_US').format(DateTime.now().toUtc()) + ' GMT';"
                                   , (indent (indentDelta * 1)) ++ "final _secretValue = Hmac(sha256, utf8.encode(_self.appkey)).convert(utf8.encode('GET|" ++ signpath ++ "|${_signbody}|${_date}'));"
                                   , (indent (indentDelta * 1)) ++ "final _headers = {"
                                   , (indent (indentDelta * 2)) ++ "'x-date': _date,"
                                   , (indent (indentDelta * 2)) ++ "'Authorization': '${_self.appid}:${_secretValue}',"
                                   , (indent (indentDelta * 2)) ++ "'x-noise': '${_noise1.toRadixString(16)}${_noise2.toRadixString(16).padLeft(8, '0')}',"
                                   , (indent (indentDelta * 2)) ++ "'x-token': _self.accessToken,"
                                   , (indent (indentDelta * 1)) ++ "};"
                                   , (indent (indentDelta * 1)) ++ "final _response = await http.get('${_self.schema}://${_self.host}:${_self.port}" ++ path ++ "?" ++ query ++ "', headers: _headers);"
                                   , (indent (indentDelta * 1)) ++ "if (_response.statusCode == 200) {"
                                   , (indent (indentDelta * 2)) ++ "final _respbody = jsonDecode(_response.body);"
                                   , (indent (indentDelta * 2)) ++ "final int _code = _respbody['code'];"
                                   , (indent (indentDelta * 2)) ++ "final _payload = _respbody['payload'];"
                                   , (indent (indentDelta * 2)) ++ "if (_code == 200) {"
                                   , (indent (indentDelta * 3)) ++ "var _data = [];"
                                   , (indent (indentDelta * 3)) ++ "for (final _e in _payload['data']) {"
                                   , (indent (indentDelta * 4)) ++ "final " ++ (toDartName name) ++ " = get" ++ pre ++ "FromJson(_e);"
                                   , (indent (indentDelta * 4)) ++ "_data.add(" ++ (toDartName name) ++ ");"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 3)) ++ "final _pagination = _payload['pagination'];"
                                   , (indent (indentDelta * 3)) ++ "return Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>(_tokensOption, Pagination<" ++ pre ++ ">(_data.cast<" ++ pre ++ ">(), _pagination['offset'], _pagination['limit']));"
                                   , (indent (indentDelta * 2)) ++ "} else if (_code == 403) {"
                                   , (indent (indentDelta * 3)) ++ "try {"
                                   , (indent (indentDelta * 4)) ++ "_tokensOption = await session.refresh(_self);"
                                   , (indent (indentDelta * 4)) ++ "_self.accessToken = _tokensOption.a;"
                                   , (indent (indentDelta * 4)) ++ "_self.refreshToken = _tokensOption.b;"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list")) ++ "(_self, _tokensOption, _countdown - 1, offset: offset, limit: limit);"
                                   , (indent (indentDelta * 3)) ++ "} on ApiException {"
                                   , (indent (indentDelta * 4)) ++ "await Future.delayed(const Duration(seconds:1));"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list")) ++ "(_self, _tokensOption, _countdown - 1, offset: offset, limit: limit);"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 2)) ++ "} else {"
                                   , (indent (indentDelta * 3)) ++ "throw ApiException(_code, _payload);"
                                   , (indent (indentDelta * 2)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "} else {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(_response.statusCode, _response.body);"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , "}"
                                   , ""
                                   , "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> " ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list")) ++ "(Caller _self, {int offset = 0, int limit = 10}) async {"
                                                                                                                                             , (indent indentDelta) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list")) ++ "(_self, Tuple<String, String>(null, null), 2, offset: offset, limit: limit);"
                                   , "}"
                                   ]

        generateFetchListsByReferences : String -> String -> String -> List1 State -> List1 Transition -> List Parameter -> String
        generateFetchListsByReferences pre name pname states transitions fields
          = List.join "\n\n" $ map (generateFetchListsByReference pre name pname states transitions) fields
          where
            generateFetchListByReference : String -> String -> String -> State -> String
            generateFetchListByReference pre name refname (MkState sname _ _ _)
              = let signpath = "/" ++ refname ++ "/${rid}/" ++ name ++ "/" ++ sname
                    path = "${_self.basePath}" ++ signpath
                    query = "limit=${limit}&offset=${offset}" in
                    List.join "\n" [ "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list-by-" ++ refname)) ++ "(Caller _self, Tuple<String, String> _tokensOption, int _countdown, BigInt rid, {int offset = 0, int limit = 10}) async {"
                                   , (indent (indentDelta * 1)) ++ "if (_countdown == 0) {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(403, '会话过期');"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "final _signbody = '" ++ query ++ "';"
                                   , (indent (indentDelta * 1)) ++ "final _noise1 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _noise2 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _date = DateFormat('EEE, dd MMM yyyy HH:mm:ss', 'en_US').format(DateTime.now().toUtc()) + ' GMT';"
                                   , (indent (indentDelta * 1)) ++ "final _secretValue = Hmac(sha256, utf8.encode(_self.appkey)).convert(utf8.encode('GET|" ++ signpath ++ "|${_signbody}|${_date}'));"
                                   , (indent (indentDelta * 1)) ++ "final _headers = {"
                                   , (indent (indentDelta * 2)) ++ "'x-date': _date,"
                                   , (indent (indentDelta * 2)) ++ "'Authorization': '${_self.appid}:${_secretValue}',"
                                   , (indent (indentDelta * 2)) ++ "'x-noise': '${_noise1.toRadixString(16)}${_noise2.toRadixString(16).padLeft(8, '0')}',"
                                   , (indent (indentDelta * 2)) ++ "'x-token': _self.accessToken,"
                                   , (indent (indentDelta * 1)) ++ "};"
                                   , (indent (indentDelta * 1)) ++ "final _response = await http.get('${_self.schema}://${_self.host}:${_self.port}" ++ path ++ "?" ++ query ++ "', headers: _headers);"
                                   , (indent (indentDelta * 1)) ++ "if (_response.statusCode == 200) {"
                                   , (indent (indentDelta * 2)) ++ "final _respbody = jsonDecode(_response.body);"
                                   , (indent (indentDelta * 2)) ++ "final int _code = _respbody['code'];"
                                   , (indent (indentDelta * 2)) ++ "final _payload = _respbody['payload'];"
                                   , (indent (indentDelta * 2)) ++ "if (_code == 200) {"
                                   , (indent (indentDelta * 3)) ++ "var _data = [];"
                                   , (indent (indentDelta * 3)) ++ "for (final _e in _payload['data']) {"
                                   , (indent (indentDelta * 4)) ++ "final " ++ (toDartName name) ++ " = get" ++ pre ++ "FromJson(_e);"
                                   , (indent (indentDelta * 4)) ++ "_data.add(" ++ (toDartName name) ++ ");"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 3)) ++ "final _pagination = _payload['pagination'];"
                                   , (indent (indentDelta * 3)) ++ "return Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>(_tokensOption, Pagination<" ++ pre ++ ">(_data.cast<" ++ pre ++ ">(), _pagination['offset'], _pagination['limit']));"
                                   , (indent (indentDelta * 2)) ++ "} else if (_code == 403) {"
                                   , (indent (indentDelta * 3)) ++ "try {"
                                   , (indent (indentDelta * 4)) ++ "_tokensOption = await session.refresh(_self);"
                                   , (indent (indentDelta * 4)) ++ "_self.accessToken = _tokensOption.a;"
                                   , (indent (indentDelta * 4)) ++ "_self.refreshToken = _tokensOption.b;"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list-by-" ++ refname)) ++ "(_self, _tokensOption, _countdown - 1, rid, offset: offset, limit: limit);"
                                   , (indent (indentDelta * 3)) ++ "} on ApiException {"
                                   , (indent (indentDelta * 4)) ++ "await Future.delayed(const Duration(seconds:1));"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list-by-" ++ refname)) ++ "(_self, _tokensOption, _countdown - 1, rid, offset: offset, limit: limit);"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 2)) ++ "} else {"
                                   , (indent (indentDelta * 3)) ++ "throw ApiException(_code, _payload);"
                                   , (indent (indentDelta * 2)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "} else {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(_response.statusCode, _response.body);"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , "}"
                                   , ""
                                   , "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> " ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list-by-" ++ refname)) ++ "(Caller _self, BigInt rid, {int offset = 0, int limit = 10}) async {"
                                                                                                                                             , (indent indentDelta) ++ "return _" ++ (toDartName ("get-" ++ sname ++ "-"  ++ name ++ "-list-by-" ++ refname)) ++ "(_self, Tuple<String, String>(null, null), 2, rid, offset: offset, limit: limit);"
                                   , "}"
                                   ]

            generateFetchListsByReference : String -> String -> String -> List1 State -> List1 Transition -> Parameter -> String
            generateFetchListsByReference pre name pname states transitions (fname, _, metas)
              = let refname = case lookup "reference" metas of
                                   Just (MVString refname') => refname'
                                   _ => fname
                    filteredStates = liftListStates states transitions
                    pairs = liftListStatesOfParticipants states transitions
                    filteredStatesOfParticipant = map (\(s, _) => s) $ filter (\(_, p) => p == pname) pairs
                    combinedStates = nubBy (\(MkState x _ _ _), (MkState y _ _ _) => x == y) (filteredStates ++ filteredStatesOfParticipant) in
                    List.join "\n\n" $ map (generateFetchListByReference pre name refname) combinedStates

        generateSearch : String -> String -> String -> String -> String
        generateSearch pre name pathPostfix namePostfix
          = let signpath = "/" ++ name ++ "/search" ++ pathPostfix
                path = "${_self.basePath}" ++ signpath
                query = "limit=${limit}&offset=${offset}&words=${json.encode(words)}" in
                List.join "\n" [ "// begin search-" ++ name ++ namePostfix
                               , "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> _" ++ (toDartName ("search-" ++ name ++ namePostfix)) ++ "(Caller _self, Tuple<String, String> _tokensOption, int _countdown, Map<String, String> words, {int offset = 0, int limit = 10}) async {"
                               , (indent (indentDelta * 1)) ++ "if (_countdown == 0) {"
                               , (indent (indentDelta * 2)) ++ "throw ApiException(403, '会话过期');"
                               , (indent (indentDelta * 1)) ++ "}"
                               , (indent (indentDelta * 1)) ++ "final _body = json.encode({'words': words, 'limit': limit, 'offset': offset});"
                               , (indent (indentDelta * 1)) ++ "final _signbody = '" ++ query ++ "';"
                               , (indent (indentDelta * 1)) ++ "final _noise1 = _self.rand.nextInt(0xFFFFFFFF);"
                               , (indent (indentDelta * 1)) ++ "final _noise2 = _self.rand.nextInt(0xFFFFFFFF);"
                               , (indent (indentDelta * 1)) ++ "final _date = DateFormat('EEE, dd MMM yyyy HH:mm:ss', 'en_US').format(DateTime.now().toUtc()) + ' GMT';"
                               , (indent (indentDelta * 1)) ++ "final _secretValue = Hmac(sha256, utf8.encode(_self.appkey)).convert(utf8.encode('POST|" ++ signpath ++ "|${_signbody}|${_date}'));"
                               , (indent (indentDelta * 1)) ++ "final _headers = {"
                               , (indent (indentDelta * 2)) ++ "'x-date': _date,"
                               , (indent (indentDelta * 2)) ++ "'Authorization': '${_self.appid}:${_secretValue}',"
                               , (indent (indentDelta * 2)) ++ "'x-noise': '${_noise1.toRadixString(16)}${_noise2.toRadixString(16).padLeft(8, '0')}',"
                               , (indent (indentDelta * 2)) ++ "'x-token': _self.accessToken,"
                               , (indent (indentDelta * 1)) ++ "};"
                               , (indent (indentDelta * 1)) ++ "final _response = await http.post('${_self.schema}://${_self.host}:${_self.port}" ++ path ++ "', headers: _headers, body: _body);"
                               , (indent (indentDelta * 1)) ++ "if (_response.statusCode == 200) {"
                               , (indent (indentDelta * 2)) ++ "final _respbody = jsonDecode(_response.body);"
                               , (indent (indentDelta * 2)) ++ "final int _code = _respbody['code'];"
                               , (indent (indentDelta * 2)) ++ "final _payload = _respbody['payload'];"
                               , (indent (indentDelta * 2)) ++ "if (_code == 200) {"
                               , (indent (indentDelta * 3)) ++ "var _data = [];"
                               , (indent (indentDelta * 3)) ++ "for (final _e in _payload['data']) {"
                               , (indent (indentDelta * 4)) ++ "final " ++ (toDartName name) ++ " = get" ++ pre ++ "FromJson(_e);"
                               , (indent (indentDelta * 4)) ++ "_data.add(" ++ (toDartName name) ++ ");"
                               , (indent (indentDelta * 3)) ++ "}"
                               , (indent (indentDelta * 3)) ++ "final _pagination = _payload['pagination'];"
                               , (indent (indentDelta * 3)) ++ "return Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>(_tokensOption, Pagination<" ++ pre ++ ">(_data.cast<" ++ pre ++ ">(), _pagination['offset'], _pagination['limit']));"
                               , (indent (indentDelta * 2)) ++ "} else if (_code == 403) {"
                               , (indent (indentDelta * 3)) ++ "try {"
                               , (indent (indentDelta * 4)) ++ "_tokensOption = await session.refresh(_self);"
                               , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("search-" ++ name ++ namePostfix)) ++ "(_self, _tokensOption, _countdown - 1, words, offset: offset, limit: limit);"
                               , (indent (indentDelta * 3)) ++ "} on ApiException {"
                               , (indent (indentDelta * 4)) ++ "await Future.delayed(const Duration(seconds:1));"
                               , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ("search-" ++ name ++ namePostfix)) ++ "(_self, _tokensOption, _countdown - 1, words, offset: offset, limit: limit);"
                               , (indent (indentDelta * 3)) ++ "}"
                               , (indent (indentDelta * 2)) ++ "} else {"
                               , (indent (indentDelta * 3)) ++ "throw ApiException(_code, _payload);"
                               , (indent (indentDelta * 2)) ++ "}"
                               , (indent (indentDelta * 1)) ++ "} else {"
                               , (indent (indentDelta * 2)) ++ "throw ApiException(_response.statusCode, _response.body);"
                               , (indent (indentDelta * 1)) ++ "}"
                               , "}"
                               , ""
                               , "Future<Tuple<Tuple<String, String>, Pagination<" ++ pre ++ ">>> " ++ (toDartName ("search-" ++ name ++ namePostfix)) ++ "(Caller _self, Map<String, String> words, {int offset = 0, int limit = 10}) async {"
                               , (indent indentDelta) ++ "return _" ++ (toDartName ("search-" ++ name ++ namePostfix)) ++ "(_self, Tuple<String, String>(null, null), 2, words, offset: offset, limit: limit);"
                               , "}"
                               , "// end search-" ++ name ++ namePostfix
                               ]

        generateStateSearchs : String -> String -> String -> List1 State -> List1 Transition -> String
        generateStateSearchs pre name pname states transitions
          = let filteredStates = liftIndexStates states transitions
                indexCode = map (\(MkState sname _ _ _) => generateSearch pre name ("/" ++ sname) ("-in-" ++ sname)) filteredStates
                pairs = liftIndexStatesOfParticipants states transitions
                filteredPairs = filter (\(_, p) => p == pname) pairs
                indexCodeOfParticipants = map (\((MkState sname _ _ _), pname) => generateSearch pre name ("/" ++ sname) ("-in-" ++ sname)) filteredPairs in
                if length indexCodeOfParticipants > 0
                   then List.join "\n\n" indexCodeOfParticipants
                   else List.join "\n\n" indexCode

        generateEvents : String -> String -> List Event -> String
        generateEvents pre name evts
          = join "\n\n" $ map (generateEvent pre name) evts
          where
            generateEvent : String -> String -> Event -> String
            generateEvent pre name evt@(MkEvent ename params metas)
              = let fsmIdStyle = fsmIdStyleOfEvent evt
                    returnType = case fsmIdStyle of
                                      FsmIdStyleGenerate => "Tuple<Tuple<String, String>, BigInt>"
                                      _ => "Tuple<Tuple<String, String>, bool>"
                    params' = case fsmIdStyle of
                                   FsmIdStyleUrl => ("_self", (TRecord "Caller" []), Nothing) :: ("_fsmid", (TPrimType PTULong), Nothing) :: params
                                   _ => ("_self", (TRecord "Caller" []), Nothing) :: params
                    params'' = case fsmIdStyle of
                                    FsmIdStyleUrl => ("_self", (TRecord "Caller" []), Nothing) :: ("_tokensOption", (TRecord "Tuple<String, String>" [], Nothing)) :: ("_countdown", (TPrimType PTUInt) , Nothing) :: ("_fsmid", (TPrimType PTULong), Nothing) :: params
                                    _ => ("_self", (TRecord "Caller" []), Nothing) :: ("_tokensOption", (TRecord "Tuple<String, String>" [], Nothing)) :: ("_countdown", (TPrimType PTUInt), Nothing) :: params
                    signpath = case fsmIdStyle of
                                    FsmIdStyleUrl => "/" ++ name ++ "/${_fsmid}/" ++ ename
                                    _ => "/" ++ name ++ "/" ++ ename
                    path = "${_self.basePath}" ++ signpath
                    return = case fsmIdStyle of
                                  FsmIdStyleGenerate => "return Tuple<Tuple<String, String>, BigInt>(_tokensOption, BigInt.parse(_respbody['payload']));"
                                  _ => "return Tuple<Tuple<String, String>, bool>(_tokensOption, _respbody['payload'] == 'Okay');"
                    in
                    List.join "\n" [ "// begin " ++ ename
                                   , "Future<" ++ returnType ++ "> _" ++ (toDartName ename) ++ "(" ++ (generateParametersSignature params'') ++ ") async {"
                                   , (indent (indentDelta * 1)) ++ "if (_countdown == 0) {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(403, '会话过期');"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "final _body = json.encode({" ++ (List.join ", " (map (\(n, t, _) => "'" ++ n ++ "': " ++ (toDartJson n t)) params)) ++ "});"
                                   , (indent (indentDelta * 1)) ++ "final _signbody = '" ++ (List.join "&" $ map generateSignatureBody $ sortBy (\(a, _, _), (b, _, _) => compare a b) params) ++ "';"
                                   , (indent (indentDelta * 1)) ++ "final _noise1 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _noise2 = _self.rand.nextInt(0xFFFFFFFF);"
                                   , (indent (indentDelta * 1)) ++ "final _date = DateFormat('EEE, dd MMM yyyy HH:mm:ss', 'en_US').format(DateTime.now().toUtc()) + ' GMT';"
                                   , (indent (indentDelta * 1)) ++ "final _secretValue = Hmac(sha256, utf8.encode(_self.appkey)).convert(utf8.encode('POST|" ++ signpath ++ "|${_signbody}|${_date}'));"
                                   , (indent (indentDelta * 1)) ++ "final _headers = {"
                                   , (indent (indentDelta * 2)) ++ "'x-date': _date,"
                                   , (indent (indentDelta * 2)) ++ "'Authorization': '${_self.appid}:${_secretValue}',"
                                   , (indent (indentDelta * 2)) ++ "'x-noise': '${_noise1.toRadixString(16)}${_noise2.toRadixString(16).padLeft(8, '0')}',"
                                   , (indent (indentDelta * 2)) ++ "'x-token': _self.accessToken,"
                                   , (indent (indentDelta * 1)) ++ "};"
                                   , (indent (indentDelta * 1)) ++ "final _response = await http.post('${_self.schema}://${_self.host}:${_self.port}" ++ path ++ "', headers: _headers, body: _body);"
                                   , (indent (indentDelta * 1)) ++ "if (_response.statusCode == 200) {"
                                   , (indent (indentDelta * 2)) ++ "final _respbody = jsonDecode(_response.body);"
                                   , (indent (indentDelta * 2)) ++ "final int _code = _respbody['code'];"
                                   , (indent (indentDelta * 2)) ++ "if (_code == 200) {"
                                   , (indent (indentDelta * 3)) ++ return
                                   , (indent (indentDelta * 2)) ++ "} else if (_code == 403) {"
                                   , (indent (indentDelta * 3)) ++ "try {"
                                   , (indent (indentDelta * 4)) ++ "_tokensOption = await session.refresh(_self);"
                                   , (indent (indentDelta * 4)) ++ "_self.accessToken = _tokensOption.a;"
                                   , (indent (indentDelta * 4)) ++ "_self.refreshToken = _tokensOption.b;"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ename) ++ "(" ++ (generateCallArguments params'') ++ ");"
                                   , (indent (indentDelta * 3)) ++ "} on ApiException {"
                                   , (indent (indentDelta * 4)) ++ "await Future.delayed(const Duration(seconds:1));"
                                   , (indent (indentDelta * 4)) ++ "_countdown -= 1;"
                                   , (indent (indentDelta * 4)) ++ "return _" ++ (toDartName ename) ++ "(" ++ (generateCallArguments params'') ++ ");"
                                   , (indent (indentDelta * 3)) ++ "}"
                                   , (indent (indentDelta * 2)) ++ "} else {"
                                   , (indent (indentDelta * 3)) ++ "throw ApiException(_code, _respbody['payload']);"
                                   , (indent (indentDelta * 2)) ++ "}"
                                   , (indent (indentDelta * 1)) ++ "} else {"
                                   , (indent (indentDelta * 2)) ++ "throw ApiException(_response.statusCode, _response.body);"
                                   , (indent (indentDelta * 1)) ++ "}"
                                   , "}"
                                   , ""
                                   , "Future<" ++ returnType ++ "> " ++ (toDartName ename) ++ "(" ++ (generateParametersSignature params') ++ ") async {"
                                   , (indent indentDelta) ++ "final _tokensOption = null;"
                                   , (indent indentDelta) ++ "final _countdown = 2;"
                                   , (indent indentDelta) ++ "return _" ++ (toDartName ename) ++ "(" ++ (generateCallArguments params'') ++ ");"
                                   , "}"
                                   ,  "// end " ++ ename
                                   ]
              where
                generateSignatureBody : Parameter -> String
                generateSignatureBody (n, (TList (TPrimType _)), _) = n ++ "=${json.encode(" ++ (toDartName n) ++ ".map((i) => i).toList())}"
                generateSignatureBody (n, (TList _), _)             = n ++ "=${json.encode(" ++ (toDartName n) ++ ".map((i) => i.toJson()).toList())}"
                generateSignatureBody (n, (TDict _ _), _)           = n ++ "=${json.encode(" ++ (toDartName n) ++ ")}"
                generateSignatureBody (n, _,           _)           = n ++ "=$" ++ (toDartName n)

                generateCallArguments : List Parameter -> String
                generateCallArguments params
                  = List.join ", " $ map (\(n, _, _) => (toDartName n)) params

generateLibrary : String
generateLibrary
  = join "\n\n" $ List.filter nonblank [ "import 'dart:math';"
                                       , "import 'dart:typed_data';"
                                       , "import 'dart:convert';"
                                       , "import 'package:crypto/crypto.dart';"
                                       , generatePagination
                                       , generateCaller
                                       , generateApiException
                                       , generateTuple
                                       , generateMd5XorUint32s
                                       , generateAddSalt
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
                       , (indent indentDelta) ++ "final String basePath;"
                       , (indent indentDelta) ++ "final String appid;"
                       , (indent indentDelta) ++ "final String appkey;"
                       , (indent indentDelta) ++ "final Random rand;"
                       , (indent indentDelta) ++ "String accessToken;"
                       , (indent indentDelta) ++ "String refreshToken;"
                       , (indent indentDelta) ++ "Caller(this.schema, this.host, this.port, this.basePath, this.appid, this.appkey, this.rand);"
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

    generateTuple : String
    generateTuple
      = List.join "\n" [ "class Tuple<A, B> {"
                       , (indent indentDelta) ++ "A a; B b;"
                       , (indent indentDelta) ++ "Tuple(this.a, this.b);"
                       , (indent indentDelta) ++ " @override bool operator ==(other) => other is Tuple<A, B> && other.a == a && other.b == b;"
                       , "}"
                       ]

    generateMd5XorUint32s : String
    generateMd5XorUint32s
      = List.join "\n" [ "Digest md5XorUint32s(List<int> md5Bytes, int a0, int a1, int a2, int a3) {"
                       , (indent indentDelta) ++ "var buffer = Uint8List(16).buffer;"
                       , (indent indentDelta) ++ "var bdata = ByteData.view(buffer);"
                       , (indent indentDelta) ++ "bdata.setUint32(0, a0);"
                       , (indent indentDelta) ++ "bdata.setUint32(4, a1);"
                       , (indent indentDelta) ++ "bdata.setUint32(8, a2);"
                       , (indent indentDelta) ++ "bdata.setUint32(12, a3);"
                       , (indent indentDelta) ++ "final bytes = Uint8List.view(buffer);"
                       , (indent indentDelta) ++ "var result = Uint8List(md5Bytes.length);"
                       , (indent indentDelta) ++ "for (var i = 0; i < md5Bytes.length; i ++) {"
                       , (indent (indentDelta * 2)) ++ "result[i] = md5Bytes[i] ^ bytes[i];"
                       , (indent indentDelta) ++ "}"
                       , (indent indentDelta) ++ "return Digest(result.toList());"
                       , "}"
                       ]

    generateAddSalt : String
    generateAddSalt
      = List.join "\n" [ "String addSalt(String password, BigInt salt) {"
                       , (indent indentDelta) ++ "final l = (salt & BigInt.from(0xFFFFFFFF)).toInt();"
                       , (indent indentDelta) ++ "final h = ((salt >> 32) & BigInt.from(0xFFFFFFFF)).toInt();"
                       , (indent indentDelta) ++ "final pwmd5 = md5.convert(utf8.encode(password));"
                       , (indent indentDelta) ++ "final passwd = md5XorUint32s(pwmd5.bytes, h, l, h, l);"
                       , (indent indentDelta) ++ "return passwd.toString();"
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
