-module(toker_c).
-compile(export_all).

-include_lib("parse_trans/include/codegen.hrl").

c(File, Opts) ->
    transform_epp(),
    Res = c:c(File, Opts),
    c:l(epp), % restore epp when done
    Res.

bootstrap_toker() ->
    code:unstick_dir(filename:dirname(code:which(epp))),
    case erlang:function_exported(erl_parse, orig_parse_form, 1) of
	true ->
	    ok;
	false ->
	    toker_c:transform_epp()
    end,
    ensure_started().

ensure_started() ->
    case whereis(toker_server) of
	undefined ->
	    toker_server:start();
	S ->
	    {ok, S}
    end.

transform_epp() ->
    parse_trans_mod:transform_module(
      epp, [fun(Fs, _Os) ->
                    parse_trans:export_function(epp_request, 2, Fs)
            end,
            fun transform_parse_erl_form/2], [report_errors,
					      report_warnings]).

transform_parse_erl_form(Forms, _Opts) ->
    NewF = codegen:gen_function(
	     parse_erl_form,
	     fun(Epp) ->
		     try
			 case epp:epp_request(Epp, scan_erl_form) of
			     {ok,Toks} ->
				 Mod = ?MODULE:get_parse_module(Toks),
				 Mod:parse_form(Toks);
			     Other ->
				 Other
			 end
		     catch
			 error:E -> io:fwrite("!!! ~p:~p~n~p~n",
					      [error,E, erlang:get_stacktrace()]),
				    erlang:error(E)
		     end
	     end),
    parse_trans:replace_function(parse_erl_form, 1, NewF, Forms).

transform_tokens(T) ->
    T.

get_token_transform(Tokens) ->
    case get_attr(toker_token_transform, Tokens) of
	undefined ->
	    toker_server:token_transform();
	P ->
	    toker_server:token_transform(P),
	    P
    end.

get_parse_module(Tokens) ->
    case get_attr(toker_parse, Tokens) of
	undefined ->
	    toker_server:parser();
	P ->
	    toker_server:parser(P),
	    P
    end.

get_attr(K, [{'-',_},{atom,_,K},
	     {'(',_},{atom,_,V},{')',_},{dot,_}|_]) ->
    V;
get_attr(K, [_|T]) ->
    get_attr(K, T);
get_attr(_, []) ->
    undefined.
