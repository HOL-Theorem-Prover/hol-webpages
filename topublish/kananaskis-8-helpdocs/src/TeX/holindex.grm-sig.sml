signature Holindex_TOKENS =
sig
type ('a,'b) token
type svalue
val EOF:  'a * 'a -> (svalue,'a) token
val COMMA:  'a * 'a -> (svalue,'a) token
val IDENT: (string) *  'a * 'a -> (svalue,'a) token
val COMMENT:  'a * 'a -> (svalue,'a) token
val LATEX:  'a * 'a -> (svalue,'a) token
val CONTENT:  'a * 'a -> (svalue,'a) token
val LABEL:  'a * 'a -> (svalue,'a) token
val OPTIONS:  'a * 'a -> (svalue,'a) token
val SHORT_INDEX:  'a * 'a -> (svalue,'a) token
val LONG_INDEX:  'a * 'a -> (svalue,'a) token
val FORCE_INDEX:  'a * 'a -> (svalue,'a) token
val STRING: (string) *  'a * 'a -> (svalue,'a) token
val IDS:  'a * 'a -> (svalue,'a) token
val THEOREMS:  'a * 'a -> (svalue,'a) token
val THEOREM:  'a * 'a -> (svalue,'a) token
val TYPE:  'a * 'a -> (svalue,'a) token
val TERM:  'a * 'a -> (svalue,'a) token
val EQUAL:  'a * 'a -> (svalue,'a) token
val RBRACKET:  'a * 'a -> (svalue,'a) token
val LBRACKET:  'a * 'a -> (svalue,'a) token
val RBRACE:  'a * 'a -> (svalue,'a) token
val LBRACE:  'a * 'a -> (svalue,'a) token
end
signature Holindex_LRVALS=
sig
structure Tokens : Holindex_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
