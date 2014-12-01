

# Module toker #
* [Data Types](#types)
* [Function Index](#index)
* [Function Details](#functions)



<a name="types"></a>

## Data Types ##




### <a name="type-key">key()</a> ###



<pre><code>
key() = any()
</code></pre>





### <a name="type-value">value()</a> ###



<pre><code>
value() = any()
</code></pre>


<a name="index"></a>

## Function Index ##


<table width="100%" border="1" cellspacing="0" cellpadding="2" summary="function index"><tr><td valign="top"><a href="#lookup-1">lookup/1</a></td><td>Retrieve a Value previously stored with store/2.</td></tr><tr><td valign="top"><a href="#start-0">start/0</a></td><td>Start the toker application, installing the parser hooks.</td></tr><tr><td valign="top"><a href="#store-2">store/2</a></td><td>Store a {Key,Value} pair (e.g.</td></tr></table>


<a name="functions"></a>

## Function Details ##

<a name="lookup-1"></a>

### lookup/1 ###


<pre><code>
lookup(Key::<a href="#type-key">key()</a>) -&gt; {<a href="#type-key">key()</a>, <a href="#type-value">value()</a>} | false
</code></pre>
<br />


Retrieve a Value previously stored with store/2.


Returns `false` if there is no corresponding `{Key, Value}` pair.
<a name="start-0"></a>

### start/0 ###

`start() -> any()`

Start the toker application, installing the parser hooks.
<a name="store-2"></a>

### store/2 ###


<pre><code>
store(Key::<a href="#type-key">key()</a>, Value::<a href="#type-value">value()</a>) -&gt; ok
</code></pre>
<br />


Store a {Key,Value} pair (e.g. macro) during parsing.


This function can be used to maintain state during parsing, and e.g.
store macro definitions for later recall using [`lookup/2`](#lookup-2).
