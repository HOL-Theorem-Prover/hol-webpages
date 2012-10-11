signature DiskFiles_TOKENS =
sig
type ('a,'b) token
type svalue
val TMC:  'a * 'a -> (svalue,'a) token
val TMV:  'a * 'a -> (svalue,'a) token
val TYOP:  'a * 'a -> (svalue,'a) token
val TYV:  'a * 'a -> (svalue,'a) token
val NUMBER: (int) *  'a * 'a -> (svalue,'a) token
val RBRACKET:  'a * 'a -> (svalue,'a) token
val LBRACKET:  'a * 'a -> (svalue,'a) token
val THEOREMS:  'a * 'a -> (svalue,'a) token
val TERMS:  'a * 'a -> (svalue,'a) token
val TYPES:  'a * 'a -> (svalue,'a) token
val IDS:  'a * 'a -> (svalue,'a) token
val BACKSLASH:  'a * 'a -> (svalue,'a) token
val RPAREN:  'a * 'a -> (svalue,'a) token
val LPAREN:  'a * 'a -> (svalue,'a) token
val FULLSTOP:  'a * 'a -> (svalue,'a) token
val DOLLAR:  'a * 'a -> (svalue,'a) token
val ID: (string) *  'a * 'a -> (svalue,'a) token
val EOF:  'a * 'a -> (svalue,'a) token
end
signature DiskFiles_LRVALS=
sig
structure Tokens : DiskFiles_TOKENS
structure ParserData:PARSER_DATA
sharing type ParserData.Token.token = Tokens.token
sharing type ParserData.svalue = Tokens.svalue
end
