-module(m1).
-export([mult/2]).
-toker_token_transform(tt1).

-tt_define(mult(A,B), A*B).

mult(A,B) ->
    ^mult(A, B).
