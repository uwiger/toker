-module(toker_rebar_plugin).

-export([pre_compile/2,
	 pre_eunit/2]).

pre_compile(Config, File) ->
    case in_deps(Config) of
	true ->
	    try_bootstrap();
	false ->
	    ok
    end.

pre_eunit(Config, File) ->
    case filename:basename(File) of
	"toker.app.src" ->
	    code:add_path(filename:join(
			    filename:dirname(
			      filename:dirname(File)), "ebin")),
	    try_bootstrap();
	_ ->
	    case in_deps(Config) of
		true  -> try_bootstrap();
		false -> ok
	    end
    end.

try_bootstrap() ->
    try  toker_c:bootstrap_toker()
    catch
	error:_E ->
	    io:fwrite(user, "Toker bootstrap failed: error:~p~n", [_E])
    end,
    ok.


in_deps(Config) ->
    Deps = rebar_config:get(Config, deps, []),
    lists:keymember(toker, 1, Deps) orelse lists:member(toker, Deps).
