.PHONY: compile deps all doc clean halfclean

deps:
	rebar get-deps

compile: deps halfclean
	rebar compile

all: compile

doc: halfclean
	rebar get-deps compile doc

clean:
	rebar clean

halfclean:
	rebar clean skip_deps=true