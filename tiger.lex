type pos = int
(* type ('a,'b) token = ('a,'b) Tokens.token *)
type lexresult = Tokens.token

val lineNum = ErrorMsg.lineNum
val linePos = ErrorMsg.linePos
fun err(p1,p2) = ErrorMsg.error p1

val numComments = ref 0

val stringToken = ref ""
val stringStrPos = ref 0

fun eof() =
let
  val pos = hd(!linePos)
in
  (if !numComments > 0 then
    (ErrorMsg.error pos "unclosed comment";
    numComments := 0)
  else if !stringStrPos > 0 then
     (ErrorMsg.error pos "unclosed string";
     stringToken := "";
     stringStrPos := 0)
  else ();
  Tokens.EOF(pos,pos))
end


%%


%header (functor TigerLexFun(structure Tokens: Tiger_TOKENS));

letter = [a-zA-Z];
digit = [0-9];
whitespace = [\t\ ]+;
newline = [\n\r]+;
strSpecial = \\\^\]|\\\^[\@A-Z\[\\\^_]|\\[abfnrtv\\\"]|\\{digit}{digit}{digit};

%s COMMENT STRING ;


%%


<INITIAL,COMMENT,STRING>{newline}    => (lineNum := !lineNum+1; linePos := yypos :: !linePos; continue());
<INITIAL,COMMENT>{whitespace} => (continue());

<INITIAL,COMMENT>"/*" => (numComments := !numComments+1; YYBEGIN COMMENT; continue());
<COMMENT>"*/" => (numComments := !numComments-1; if !numComments = 0 then YYBEGIN INITIAL else (); continue());
<COMMENT>. => (continue());

<INITIAL>"type"     => (Tokens.TYPE(yypos, yypos + size yytext));
<INITIAL>"var"      => (Tokens.VAR(yypos, yypos + size yytext));
<INITIAL>"function" => (Tokens.FUNCTION(yypos, yypos + size yytext));
<INITIAL>"break"    => (Tokens.BREAK(yypos, yypos + size yytext));
<INITIAL>"of"       => (Tokens.OF(yypos, yypos + size yytext));
<INITIAL>"end"      => (Tokens.END(yypos, yypos + size yytext));
<INITIAL>"in"       => (Tokens.IN(yypos, yypos + size yytext));
<INITIAL>"nil"      => (Tokens.NIL(yypos, yypos + size yytext));
<INITIAL>"let"      => (Tokens.LET(yypos, yypos + size yytext));
<INITIAL>"do"       => (Tokens.DO(yypos, yypos + size yytext));
<INITIAL>"to"       => (Tokens.TO(yypos, yypos + size yytext));
<INITIAL>"for"      => (Tokens.FOR(yypos, yypos + size yytext));
<INITIAL>"while"    => (Tokens.WHILE(yypos, yypos + size yytext));
<INITIAL>"else"     => (Tokens.ELSE(yypos, yypos + size yytext));
<INITIAL>"then"     => (Tokens.THEN(yypos, yypos + size yytext));
<INITIAL>"if"       => (Tokens.IF(yypos, yypos + size yytext));
<INITIAL>"array"    => (Tokens.ARRAY(yypos, yypos + size yytext));
<INITIAL>"class"    => (Tokens.CLASS(yypos, yypos + size yytext));
<INITIAL>"extends"  => (Tokens.EXTENDS(yypos, yypos + size yytext));
<INITIAL>"method"   => (Tokens.METHOD(yypos, yypos + size yytext));
<INITIAL>"new"      => (Tokens.NEW(yypos, yypos + size yytext));

<INITIAL>":=" => (Tokens.ASSIGN(yypos, yypos + size yytext));
<INITIAL>"|"  => (Tokens.OR(yypos, yypos + size yytext));
<INITIAL>"&"  => (Tokens.AND(yypos, yypos + size yytext));
<INITIAL>">=" => (Tokens.GE(yypos, yypos + size yytext));
<INITIAL>">"  => (Tokens.GT(yypos, yypos + size yytext));
<INITIAL>"<=" => (Tokens.LE(yypos, yypos + size yytext));
<INITIAL>"<"  => (Tokens.LT(yypos, yypos + size yytext));
<INITIAL>"<>" => (Tokens.NEQ(yypos, yypos + size yytext));
<INITIAL>"="  => (Tokens.EQ(yypos, yypos + size yytext));
<INITIAL>"/"  => (Tokens.DIVIDE(yypos, yypos + size yytext));
<INITIAL>"*"  => (Tokens.TIMES(yypos, yypos + size yytext));
<INITIAL>"-"  => (Tokens.MINUS(yypos, yypos + size yytext));
<INITIAL>"+"  => (Tokens.PLUS(yypos, yypos + size yytext));
<INITIAL>"."  => (Tokens.DOT(yypos, yypos + size yytext));
<INITIAL>"}"  => (Tokens.RBRACE(yypos, yypos + size yytext));
<INITIAL>"{"  => (Tokens.LBRACE(yypos, yypos + size yytext));
<INITIAL>"]"  => (Tokens.RBRACK(yypos, yypos + size yytext));
<INITIAL>"["  => (Tokens.LBRACK(yypos, yypos + size yytext));
<INITIAL>")"  => (Tokens.RPAREN(yypos, yypos + size yytext));
<INITIAL>"("  => (Tokens.LPAREN(yypos, yypos + size yytext));
<INITIAL>";"  => (Tokens.SEMICOLON(yypos, yypos + size yytext));
<INITIAL>":"  => (Tokens.COLON(yypos, yypos + size yytext));
<INITIAL>","  => (Tokens.COMMA(yypos, yypos + size yytext));

<INITIAL>\"               => (stringStrPos := yypos; stringToken := ""; YYBEGIN STRING; continue());
<STRING>{strSpecial}      => (stringToken := !stringToken ^ valOf(String.fromString yytext); continue());
<STRING>\\[\ \t\n\r\f]+\\ => (continue());
<STRING>\\.               => (ErrorMsg.error yypos ("illegal escaped character in string '" ^ yytext ^ "'"); continue());
<STRING>\"                => (YYBEGIN INITIAL; let val si = !stringStrPos in (stringStrPos := 0; Tokens.STRING(!stringToken, si, yypos+1)) end);
<STRING>.                 => (stringToken := !stringToken ^ yytext; continue());

<INITIAL>{digit}+ => (Tokens.INT(valOf(Int.fromString yytext), yypos, yypos + size yytext));

<INITIAL>{letter}[a-zA-Z0-9_]* => (Tokens.ID(yytext, yypos, yypos + size yytext));

<INITIAL>. => (ErrorMsg.error yypos ("illegal character '" ^ yytext ^ "'"); continue());
