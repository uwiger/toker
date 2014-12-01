.PHONY: compile deps all doc test clean halfclean

deps:
	rebar get-deps

compile: deps halfclean
	rebar compile

all: compile

doc: halfclean
	rebar get-deps compile doc

test: compile
	rebar eunit skip_deps=true

clean:
	rebar clean

halfclean:
	rebar clean skip_deps=true