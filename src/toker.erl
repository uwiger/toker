-module(toker).

-export([start/0,
	 store/2,
	 lookup/1]).

-type key()   :: any().
-type value() :: any().

%% @doc Start the toker application, installing the parser hooks.
start() ->
    application:start(toker).


-spec store(key(), value()) -> ok.
%% @doc Store a {Key,Value} pair (e.g. macro) during parsing.
%%
%% This function can be used to maintain state during parsing, and e.g.
%% store macro definitions for later recall using {@link lookup/2}.
%% @end
store(Key, Value) ->
    toker_server:store(Key, Value).

-spec lookup(key()) -> {key(), value()} | false.
%% @doc Retrieve a Value previously stored with store/2.
%%
%% Returns `false' if there is no corresponding `{Key, Value}' pair.
%% @end
lookup(Key) ->
    toker_server:lookup(Key).
