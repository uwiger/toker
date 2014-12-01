-module(toker_server).

-behaviour(gen_server).

-export([parser/0, parser/1, reset/1,
	 store/2, lookup/1,
	 token_transform/0, token_transform/1]).
-export([stop/0]).
-export([start/0,
	 start_link/0,
	 init/1,
	 handle_call/3,
	 handle_cast/2,
	 handle_info/2,
	 terminate/2,
	 code_change/3]).

-record(st, {parsers = [],
	     default_parser = erl_parse,
	     token_transformers = [],
	     dict = [],
	     default_token_transformer = toker_c,
	     monitors = [],
	     pending_stop = []}).

start()      -> gen_server:start({local, ?MODULE}, ?MODULE, [], []).
start_link() -> gen_server:start_link({local,?MODULE}, ?MODULE, [], []).

parser()  -> call(parser).
parser(P) -> call({parser, P}).

token_transform()  -> call(token_transform).
token_transform(T) -> call({token_transform, T}).

-spec store(any(), any()) -> ok.
store(K, V) ->
    call({store, K, V}).

-spec lookup(any()) -> any() | undefined.
lookup(K) ->
    call({lookup, K}).

reset(C) when C==parser; C==token_transform; C==dict; C==all ->
    call({reset, C}).

stop() ->
    case whereis(?MODULE) of
	undefined -> ok;
	_ -> call(stop)
    end.

call(Req) ->
    gen_server:call(?MODULE, Req).

init(_) ->
    _ = toker_c:bootstrap_toker(),
    {ok, #st{}}.

handle_call(parser, {P,_}, #st{parsers = Ps} = St) ->
    case lists:keyfind(P, 1, Ps) of
	{_, Parser} -> {reply, Parser, St};
	false       -> {reply, St#st.default_parser, St}
    end;
handle_call(token_transform, {P,_}, #st{token_transformers = Ts} = St) ->
    case lists:keyfind(P, 1, Ts) of
	{_, Transform} -> {reply, Transform, St};
	false          -> {reply, St#st.default_token_transformer, St}
    end;
handle_call({parser, P}, {Pid,_}, #st{parsers = Ps,
				     monitors = Ms} = St) ->
    Ms1 = ensure_monitor(Pid, Ms),
    {reply, ok, St#st{parsers = lists:keystore(Pid, 1, Ps, {Pid, P}),
		      monitors = Ms1}};
handle_call({token_transform, T}, {Pid,_}, #st{token_transformers = Ts,
					       monitors = Ms} = St) ->
    Ms1 = ensure_monitor(Pid, Ms),
    {reply, ok, St#st{token_transformers = lists:keystore(Pid, 1, Ts, {Pid, T}),
		      monitors = Ms1}};
handle_call({store, K, V}, {Pid,_}, #st{dict = D} = St) ->
    Key = {Pid, K},
    {reply, ok, St#st{dict = lists:keystore(Key, 1, D, {Key, V})}};
handle_call({lookup, K}, {Pid,_}, #st{dict = D} = St) ->
    {reply, case lists:keyfind({Pid,K}, 1, D) of
		{_, V} -> {K, V};
		false  -> false
	    end, St};
handle_call({reset, C}, {Pid,_}, #st{parsers = Ps,
				     token_transformers = Ts,
				     dict = D,
				     monitors = Ms} = St) ->
    {Ps1, Ts1, D1, Ms1} = case C of
			      parser ->
				  {lists:keydelete(Pid,1,Ps),Ts,D,Ms};
			      token_transform ->
				  {Ps, lists:keydelete(Pid,1,Ts),D,Ms};
			      dict ->
				  {Ps,Ts,dict_reset(Pid, D), Ms};
			      all ->
				  {lists:keydelete(Pid,1,Ps),
				   lists:keydelete(Pid,1,Ts),
				   dict_reset(Pid, D),
				   lists:keydelete(Pid,2,Ms)}
		      end,
    {reply, ok, St#st{parsers = Ps1, token_transformers = Ts1,
		      dict = D1, monitors = Ms1}};
handle_call(stop, From, #st{monitors = Ms} = St) ->
    if Ms == [] ->
	    {stop, normal, ok, St};
       true ->
	    {noreply, St#st{pending_stop = [From|St#st.pending_stop]}}
    end;
handle_call(_, _, St) ->
    {reply, error, St}.

handle_cast(_, St) ->
    {noreply, St}.

handle_info({'DOWN',Ref,_,_,_}, #st{parsers = Ps,
				    token_transformers = Ts,
				    monitors = Ms} = St) ->
    case lists:keyfind(Ref, 1, Ms) of
	{Ref, Pid} ->
	    check_pending(
	      St#st{parsers = lists:keydelete(Pid,1,Ps),
		    token_transformers = lists:keydelete(Pid,1,Ts),
		    monitors = lists:keydelete(Ref, 1, Ms)});
	false ->
	    {noreply, St}
    end.

check_pending(#st{pending_stop = []} = St) ->
    {noreply, St};
check_pending(#st{pending_stop = [_|_] = Pend, monitors = []} = St) ->
    [gen_server:reply(From, ok) || From <- Pend],
    {stop, normal, St}.

terminate(_, _) ->
    ok.

code_change(_, S, _) ->
    {ok, S}.

ensure_monitor(Pid, Ms) ->
    case lists:keymember(Pid, 2, Ms) of
	true ->
	    Ms;
	false ->
	    Ref = erlang:monitor(process, Pid),
	    [{Ref, Pid}|Ms]
    end.

dict_reset(Pid, D) ->
    [X || {{P,_},_} = X <- D,
	  P =/= Pid].
