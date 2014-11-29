-module(toker_test).

-export([double/1, i2l/1]).

-toker_parse(toker_erl_parse).

double(L) ->
    lists:map(`(X) -> X*2`, L).

i2l(L) ->
    lists:map(`integer_to_list/1, L).
