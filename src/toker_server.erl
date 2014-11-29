-module(toker_server).

-behaviour(gen_server).

-export([parser/0, parser/1, reset/1,
	 token_transform/0, token_transform/1]).

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
	     default_token_transformer = toker_c,
	     monitors = []}).

start()      -> gen_server:start({local, ?MODULE}, ?MODULE, [], []).
start_link() -> gen_server:start_link({local,?MODULE}, ?MODULE, [], []).

parser()  -> gen_server:call(?MODULE, parser).
parser(P) -> gen_server:call(?MODULE, {parser, P}).

token_transform()  -> gen_server:call(?MODULE, token_transform).
token_transform(T) -> gen_server:call(?MODULE, {token_transform, T}).

reset(C) when C==parser; C==token_transform; C==all ->
    gen_server:call({reset, C}).

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
handle_call({reset, C}, {Pid,_}, #st{parsers = Ps,
				     token_transformers = Ts,
				     monitors = Ms} = St) ->
    {Ps1, Ts1, Ms1} = case C of
			  parser ->
			      {lists:keydelete(Pid,1,Ps),Ts,Ms};
			  token_transform ->
			      {Ps, lists:keydelete(Pid,1,Ts), Ms};
			  all ->
			      {lists:keydelete(Pid,1,Ps),
			       lists:keydelete(Pid,1,Ts),
			       lists:keydelete(Pid,2,Ms)}
		      end,
    {reply, ok, St#st{parsers = Ps1, token_transformers = Ts1,
		      monitors = Ms1}};
handle_call(_, _, St) ->
    {reply, error, St}.

handle_cast(_, St) ->
    {noreply, St}.

handle_info({'DOWN',Ref,_,_,_}, #st{parsers = Ps,
				    token_transformers = Ts,
				    monitors = Ms} = St) ->
    case lists:keyfind(Ref, 1, Ms) of
	{Ref, Pid} ->
	    {noreply, St#st{parsers = lists:keydelete(Pid,1,Ps),
			    token_transformers = lists:keydelete(Pid,1,Ts),
			    monitors = lists:keydelete(Ref, 1, Ms)}};
	false ->
	    {noreply, St}
    end.

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
