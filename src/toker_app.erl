-module(toker_app).

-behaviour(application).

%% Application callbacks
-export([start/2, stop/1]).

%% ===================================================================
%% Application callbacks
%% ===================================================================

start(_StartType, _StartArgs) ->
    toker_sup:start_link().

stop(_State) ->
    toker_c:restore(),
    ok.
