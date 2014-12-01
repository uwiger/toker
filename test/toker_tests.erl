-module(toker_tests).

-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").

t_test_() ->
    {setup,
     fun toker_setup/0,
     fun toker_cleanup/1,
     [
      ?_test(compile_m1())
     ]}.

toker_setup() ->
    toker:start().

toker_cleanup(_) ->
    application:stop(toker).

compile_m1() ->
    io:fwrite(user, "compile_m1()~n", []),
    D = filename:join(code:lib_dir(toker), "examples"),
    {ok,tt1} = compile:file(filename:join(D, "tt1"),
			    [{outdir, "."}, report]),
    {ok,m1} = compile:file(filename:join(D, "m1"), [{outdir,"."},report]),
    12 = m1:mult(3,4),
    ok.

-endif.
