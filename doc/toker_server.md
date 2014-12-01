

# Module toker_server #
* [Function Index](#index)
* [Function Details](#functions)

__Behaviours:__ [`gen_server`](gen_server.md).
<a name="index"></a>

## Function Index ##


<table width="100%" border="1" cellspacing="0" cellpadding="2" summary="function index"><tr><td valign="top"><a href="#code_change-3">code_change/3</a></td><td></td></tr><tr><td valign="top"><a href="#handle_call-3">handle_call/3</a></td><td></td></tr><tr><td valign="top"><a href="#handle_cast-2">handle_cast/2</a></td><td></td></tr><tr><td valign="top"><a href="#handle_info-2">handle_info/2</a></td><td></td></tr><tr><td valign="top"><a href="#init-1">init/1</a></td><td></td></tr><tr><td valign="top"><a href="#lookup-1">lookup/1</a></td><td></td></tr><tr><td valign="top"><a href="#parser-0">parser/0</a></td><td></td></tr><tr><td valign="top"><a href="#parser-1">parser/1</a></td><td></td></tr><tr><td valign="top"><a href="#reset-1">reset/1</a></td><td></td></tr><tr><td valign="top"><a href="#start-0">start/0</a></td><td></td></tr><tr><td valign="top"><a href="#start_link-0">start_link/0</a></td><td></td></tr><tr><td valign="top"><a href="#stop-0">stop/0</a></td><td></td></tr><tr><td valign="top"><a href="#store-2">store/2</a></td><td></td></tr><tr><td valign="top"><a href="#terminate-2">terminate/2</a></td><td></td></tr><tr><td valign="top"><a href="#token_transform-0">token_transform/0</a></td><td></td></tr><tr><td valign="top"><a href="#token_transform-1">token_transform/1</a></td><td></td></tr></table>


<a name="functions"></a>

## Function Details ##

<a name="code_change-3"></a>

### code_change/3 ###

`code_change(X1, S, X3) -> any()`


<a name="handle_call-3"></a>

### handle_call/3 ###

`handle_call(X1, From, St) -> any()`


<a name="handle_cast-2"></a>

### handle_cast/2 ###

`handle_cast(X1, St) -> any()`


<a name="handle_info-2"></a>

### handle_info/2 ###

`handle_info(X1, St) -> any()`


<a name="init-1"></a>

### init/1 ###

`init(X1) -> any()`


<a name="lookup-1"></a>

### lookup/1 ###


<pre><code>
lookup(K::any()) -&gt; any() | undefined
</code></pre>
<br />


<a name="parser-0"></a>

### parser/0 ###

`parser() -> any()`


<a name="parser-1"></a>

### parser/1 ###

`parser(P) -> any()`


<a name="reset-1"></a>

### reset/1 ###

`reset(C) -> any()`


<a name="start-0"></a>

### start/0 ###

`start() -> any()`


<a name="start_link-0"></a>

### start_link/0 ###

`start_link() -> any()`


<a name="stop-0"></a>

### stop/0 ###

`stop() -> any()`


<a name="store-2"></a>

### store/2 ###


<pre><code>
store(K::any(), V::any()) -&gt; ok
</code></pre>
<br />


<a name="terminate-2"></a>

### terminate/2 ###

`terminate(X1, X2) -> any()`


<a name="token_transform-0"></a>

### token_transform/0 ###

`token_transform() -> any()`


<a name="token_transform-1"></a>

### token_transform/1 ###

`token_transform(T) -> any()`


