-module(toker_pt).

-export([parse_transform/2]).


parse_transform(Forms, _) ->
    try toker_c:bootstrap_toker()
    catch C:E ->
	    io:fwrite("*** ~p:~p~n", [C,E])
    end,
    Forms.
