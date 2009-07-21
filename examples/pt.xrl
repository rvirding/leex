%% File    : pt.xrl
%% Author  : Robert Virding
%% Purpose : A very simple example of pushing back characters.

Definitions.

D	= [0-9]
L	= [a-zA-ZqQ]

Rules.

the	: {token,{the,TokenLine},"kalle"}.
{L}+	: {token,{word,TokenLine,TokenChars}}.
abc{D}+	: {skip_token,"sture" ++ string:substr(TokenChars, 4)}.
{D}+	: {token,{integer,TokenLine,list_to_integer(TokenChars)}}.
\s	: skip_token.
\r\n	: {end_token,{crlf,TokenLine}}.

Erlang code.
