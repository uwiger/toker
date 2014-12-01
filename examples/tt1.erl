-module(tt1).

-export([transform_tokens/1]).


transform_tokens(Ts) ->
    expand(check_defines(Ts)).

check_defines([{'-',L},{atom,_,tt_define},{'(',_},{atom,_,Name},{'(',_}|T]) ->
    {Args, [{',',_}|T1]} = collect_args(T),
    Body = get_body(T1),
    toker:store(Name, {Args, Body}),
    [{'-',L},{atom,L,tt_define},{'(',L},{atom,L,Name},{')',L},{dot,L}];
check_defines(Ts) ->
    Ts.

expand(Ts) ->
    expand_(Ts).

expand_([{'^',_},{atom,_,Name}|T]) ->
    {M, T1} = expand_macro(Name, T),
    M ++ expand_(T1);
expand_([H|T]) ->
    [H|expand_(T)];
expand_([]) ->
    [].

expand_macro(Name, [{'(',_}|Ts]) ->
    case toker:lookup(Name) of
	{_, {Args, Body}} ->
	    {Params, Ts1} = match_params(Args, Ts),
	    {substitute(Body, Params), Ts1}
    end.

match_params(Args, Ts) ->
    match_params(Args, Ts, []).

match_params([H|T], Ts, Acc) ->
    case get_param(Ts) of
	{P,[{',',_}|Ts1]} when T=/=[] ->
	    match_params(T, Ts1, [{H,P}|Acc]);
	{P,[{')',_}|Ts1]} when T==[] ->
	    {lists:reverse([{H,P}|Acc]), Ts1}
    end;
match_params([], [{')',_}|Ts], Acc) ->
    {lists:reverse(Acc), Ts}.

get_param([{'[',_}=H|T]) ->
    {Ts, Rest} = get_until(']',  '[', T),
    {[H|Ts], Rest};
get_param([{'{',_}=H|T]) ->
    {Ts, Rest} = get_until('}', '{', T),
    {[H|Ts], Rest};
get_param([H|T]) ->
    {[H], T}.

get_until(End, St, Ts) ->
    get_until(End, St, Ts, []).

get_until(End, _St, [H|T], Acc) when element(1,H) == End ->
    {lists:reverse([H|Acc]), T};
get_until(End, St, [H|T], Acc) when element(1,H) == St ->
    {Sub, T1} = get_until(End, St, T),
    get_until(End, St, T1, lists:reverse([H|Sub]) ++ Acc).

substitute([H|T], Params) when is_atom(H) ->
    {_, P} = lists:keyfind(H, 1, Params),
    P ++ substitute(T, Params);
substitute([H|T], Params) when is_list(H) ->
    H ++ substitute(T, Params);
substitute([], _) ->
    [].

collect_args([{')',_}|Ts]) ->
    {[], Ts};
collect_args([{var,_,V}|Ts]) ->
    collect_args(Ts, [V]).

collect_args([{',',_},{var,_,V}|T], Acc) ->
    collect_args(T, [V|Acc]);
collect_args([{')',_}|T], Acc) ->
    {lists:reverse(Acc), T}.

get_body(Ts) ->
    get_body(Ts, []).

get_body([{')',_},{dot,_}], Acc) ->
    [lists:reverse(Acc)];
get_body([{var,_,V}|T], Acc) ->
    [lists:reverse(Acc), V | get_body(T, [])];
get_body([H|T], Acc) ->
    get_body(T, [H|Acc]).
