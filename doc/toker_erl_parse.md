

# Module toker_erl_parse #
* [Data Types](#types)
* [Function Index](#index)
* [Function Details](#functions)



<a name="types"></a>

## Data Types ##




### <a name="type-abstract_clause">abstract_clause()</a> ###



<pre><code>
abstract_clause() = term()
</code></pre>





### <a name="type-abstract_expr">abstract_expr()</a> ###



<pre><code>
abstract_expr() = term()
</code></pre>





### <a name="type-abstract_form">abstract_form()</a> ###



<pre><code>
abstract_form() = term()
</code></pre>





### <a name="type-error_description">error_description()</a> ###



<pre><code>
error_description() = term()
</code></pre>





### <a name="type-error_info">error_info()</a> ###



<pre><code>
error_info() = {<a href="erl_scan.md#type-line">erl_scan:line()</a>, module(), <a href="#type-error_description">error_description()</a>}
</code></pre>





### <a name="type-pre_op">pre_op()</a> ###



<pre><code>
pre_op() = 'catch' | '+' | '-' | 'bnot' | 'not' | '#'
</code></pre>





### <a name="type-token">token()</a> ###



<pre><code>
token() = {Tag::atom(), Line::<a href="erl_scan.md#type-line">erl_scan:line()</a>}
</code></pre>





### <a name="type-yecc_ret">yecc_ret()</a> ###



<pre><code>
yecc_ret() = {error, term()} | {ok, term()}
</code></pre>


<a name="index"></a>

## Function Index ##


<table width="100%" border="1" cellspacing="0" cellpadding="2" summary="function index"><tr><td valign="top"><a href="#abstract-1">abstract/1</a></td><td></td></tr><tr><td valign="top"><a href="#abstract-2">abstract/2</a></td><td></td></tr><tr><td valign="top"><a href="#format_error-1">format_error/1</a></td><td></td></tr><tr><td valign="top"><a href="#func_prec-0">func_prec/0</a></td><td></td></tr><tr><td valign="top"><a href="#get_attribute-2">get_attribute/2</a></td><td></td></tr><tr><td valign="top"><a href="#get_attributes-1">get_attributes/1</a></td><td></td></tr><tr><td valign="top"><a href="#inop_prec-1">inop_prec/1</a></td><td></td></tr><tr><td valign="top"><a href="#max_prec-0">max_prec/0</a></td><td></td></tr><tr><td valign="top"><a href="#normalise-1">normalise/1</a></td><td></td></tr><tr><td valign="top"><a href="#package_segments-1">package_segments/1</a></td><td></td></tr><tr><td valign="top"><a href="#parse-1">parse/1</a></td><td></td></tr><tr><td valign="top"><a href="#parse_and_scan-1">parse_and_scan/1</a></td><td></td></tr><tr><td valign="top"><a href="#parse_exprs-1">parse_exprs/1</a></td><td></td></tr><tr><td valign="top"><a href="#parse_form-1">parse_form/1</a></td><td></td></tr><tr><td valign="top"><a href="#parse_term-1">parse_term/1</a></td><td></td></tr><tr><td valign="top"><a href="#preop_prec-1">preop_prec/1</a></td><td></td></tr><tr><td valign="top"><a href="#set_line-2">set_line/2</a></td><td></td></tr><tr><td valign="top"><a href="#tokens-1">tokens/1</a></td><td></td></tr><tr><td valign="top"><a href="#tokens-2">tokens/2</a></td><td></td></tr></table>


<a name="functions"></a>

## Function Details ##

<a name="abstract-1"></a>

### abstract/1 ###


<pre><code>
abstract(Data) -&gt; AbsTerm
</code></pre>

<ul class="definitions"><li><code>Data = term()</code></li><li><code>AbsTerm = <a href="#type-abstract_expr">abstract_expr()</a></code></li></ul>


<a name="abstract-2"></a>

### abstract/2 ###

`abstract(T, Line) -> any()`


<a name="format_error-1"></a>

### format_error/1 ###


<pre><code>
format_error(Message::any()) -&gt; [char() | list()]
</code></pre>
<br />


<a name="func_prec-0"></a>

### func_prec/0 ###


<pre><code>
func_prec() -&gt; {800, 700}
</code></pre>
<br />


<a name="get_attribute-2"></a>

### get_attribute/2 ###

`get_attribute(L, Name) -> any()`


<a name="get_attributes-1"></a>

### get_attributes/1 ###

`get_attributes(L) -> any()`


<a name="inop_prec-1"></a>

### inop_prec/1 ###

`inop_prec(X1) -> any()`


<a name="max_prec-0"></a>

### max_prec/0 ###


<pre><code>
max_prec() -&gt; 1000
</code></pre>
<br />


<a name="normalise-1"></a>

### normalise/1 ###


<pre><code>
normalise(AbsTerm) -&gt; Data
</code></pre>

<ul class="definitions"><li><code>AbsTerm = <a href="#type-abstract_expr">abstract_expr()</a></code></li><li><code>Data = term()</code></li></ul>


<a name="package_segments-1"></a>

### package_segments/1 ###

`package_segments(Name) -> any()`


<a name="parse-1"></a>

### parse/1 ###


<pre><code>
parse(Tokens::list()) -&gt; <a href="#type-yecc_ret">yecc_ret()</a>
</code></pre>
<br />


<a name="parse_and_scan-1"></a>

### parse_and_scan/1 ###


<pre><code>
parse_and_scan(X1::{function() | {atom(), atom()}, [term()]} | {atom(), atom(), [term()]}) -&gt; <a href="#type-yecc_ret">yecc_ret()</a>
</code></pre>
<br />


<a name="parse_exprs-1"></a>

### parse_exprs/1 ###


<pre><code>
parse_exprs(Tokens) -&gt; {ok, ExprList} | {error, ErrorInfo}
</code></pre>

<ul class="definitions"><li><code>Tokens = [<a href="#type-token">token()</a>]</code></li><li><code>ExprList = [<a href="#type-abstract_expr">abstract_expr()</a>]</code></li><li><code>ErrorInfo = <a href="#type-error_info">error_info()</a></code></li></ul>


<a name="parse_form-1"></a>

### parse_form/1 ###


<pre><code>
parse_form(Tokens) -&gt; {ok, AbsForm} | {error, ErrorInfo}
</code></pre>

<ul class="definitions"><li><code>Tokens = [<a href="#type-token">token()</a>]</code></li><li><code>AbsForm = <a href="#type-abstract_form">abstract_form()</a></code></li><li><code>ErrorInfo = <a href="#type-error_info">error_info()</a></code></li></ul>


<a name="parse_term-1"></a>

### parse_term/1 ###


<pre><code>
parse_term(Tokens) -&gt; {ok, Term} | {error, ErrorInfo}
</code></pre>

<ul class="definitions"><li><code>Tokens = [<a href="#type-token">token()</a>]</code></li><li><code>Term = term()</code></li><li><code>ErrorInfo = <a href="#type-error_info">error_info()</a></code></li></ul>


<a name="preop_prec-1"></a>

### preop_prec/1 ###


<pre><code>
preop_prec(X1::<a href="#type-pre_op">pre_op()</a>) -&gt; {0 | 600 | 700, 100 | 700 | 800}
</code></pre>
<br />


<a name="set_line-2"></a>

### set_line/2 ###

`set_line(L, F) -> any()`


<a name="tokens-1"></a>

### tokens/1 ###


<pre><code>
tokens(AbsTerm) -&gt; Tokens
</code></pre>

<ul class="definitions"><li><code>AbsTerm = <a href="#type-abstract_expr">abstract_expr()</a></code></li><li><code>Tokens = [<a href="#type-token">token()</a>]</code></li></ul>


<a name="tokens-2"></a>

### tokens/2 ###


<pre><code>
tokens(AbsTerm, MoreTokens) -&gt; Tokens
</code></pre>

<ul class="definitions"><li><code>AbsTerm = <a href="#type-abstract_expr">abstract_expr()</a></code></li><li><code>MoreTokens = [<a href="#type-token">token()</a>]</code></li><li><code>Tokens = [<a href="#type-token">token()</a>]</code></li></ul>


