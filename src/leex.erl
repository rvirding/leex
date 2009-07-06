%% Copyright (c) 2008 Robert Virding. All rights reserved.
%%
%% Redistribution and use in source and binary forms, with or without
%% modification, are permitted provided that the following conditions
%% are met:
%%
%% 1. Redistributions of source code must retain the above copyright
%% notice, this list of conditions and the following disclaimer.
%% 2. Redistributions in binary form must reproduce the above copyright
%% notice, this list of conditions and the following disclaimer in the
%% documentation and/or other materials provided with the distribution.
%%
%% THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
%% "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
%% LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
%% FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
%% COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
%% INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
%% BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
%% LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
%% CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
%% LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
%% ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
%% POSSIBILITY OF SUCH DAMAGE.

%%% A Lexical Analyser Generator for Erlang.
%%%
%%% Most of the algorithms used here are taken pretty much as
%%% described in the "Dragon Book" by Aho, Sethi and Ullman. Some
%%% completing details were taken from "Compiler Design in C" by
%%% Hollub.

-module(leex).

-export([compile/3,file/1,file/2,format_error/1]).

-import(lists, [member/2,reverse/1,sort/1,keysearch/3,keysort/2,
                map/2,foldl/3,foreach/2,flatmap/2,
                delete/2,keydelete/3]).
-import(string, [substr/2,substr/3,span/2,tokens/2]).
-import(ordsets, [is_element/2,add_element/2,union/2]).
-import(orddict, [store/3]).

-include("erl_compile.hrl").

-define(LEEXINC, "leexinc.hrl").        % Include file

-define(DEFS_HEAD, "Definitions.").
-define(RULE_HEAD, "Rules.").
-define(CODE_HEAD, "Erlang code.").

-record(leex, {xfile=[],        % Xrl file
               efile=[],        % Erl file
               ifile=[],        % Include file
               gfile=[],        % Graph file
               module,          % Module name
               opts=[],         % Options
               errors=[],
               warnings=[]
              }).

-record(nfa_state, {no,edges=[],accept=noaccept}).
-record(dfa_state, {no,nfa=[],trans=[],accept=noaccept}).

%%%
%%% Exported functions
%%%

%%% Interface to erl_compile.

compile(Input0, Output0,
        #options{warning = WarnLevel, verbose=Verbose, includes=Includes}) ->
    Input = assure_extension(shorten_filename(Input0), ".xrl"),
    Output = assure_extension(shorten_filename(Output0), ".erl"),
    Includefile = lists:sublist(Includes, 1),
    Opts = [{scannerfile,Output},{includefile,Includefile},{verbose,Verbose},
            {report_errors,true},{report_warnings,WarnLevel > 0}],
    case file(Input, Opts) of
        {ok, _} ->
            ok;
        error ->
            error
    end.

%% file(File) -> ok | error.
%% file(File, Options) -> ok | error.

file(File) -> file(File, []).

file(File, Opts0) ->
    case is_filename(File) of
        no -> erlang:error(badarg, [File,Opts0]);
        _ -> ok
    end,
    Opts = case options(Opts0) of
               badarg ->
                   erlang:error(badarg, [File,Opts0]);
               Options ->
                   Options
           end,
    St0 = #leex{},
    St1 = filenames(File, Opts, St0),   % Get all the filenames
    St = try
             {ok,REAs,Actions,Code,St2} = parse_file(St1),
             {DFA,DF} = make_dfa(REAs, St2),
             St3 = out_file(St2, DFA, DF, Actions, Code),
             case lists:member(dfa_graph, St3#leex.opts) of
                 true -> out_dfa_graph(St3, DFA, DF);
                 false -> St3
             end
         catch #leex{}=St4 ->
             St4
         end,
    leex_ret(St).             

format_error({file_error, Reason}) ->
    io_lib:fwrite("~s",[file:format_error(Reason)]);
format_error(missing_defs) -> "missing Definitions";
format_error(missing_rules) -> "missing Rules";
format_error(missing_code) -> "missing Erlang code";
format_error(empty_rules) -> "no rules";
format_error(bad_rule) -> "bad rule";
format_error({regexp,E})-> ["bad regexp `",regexp:format_error(E),"'"];
format_error({after_regexp,S}) ->
    ["bad code after regexp ",io_lib:write_string(S)];
format_error(ignored_characters) ->
    "ignored characters";
format_error(not_yet_implemented) ->
    "anchoring a regular expression with ^ and $ is not yet implemented".

%%%
%%% Local functions
%%%

assure_extension(File, Ext) ->
    lists:concat([strip_extension(File, Ext), Ext]).

%% Assumes File is a filename.
strip_extension(File, Ext) ->
    case filename:extension(File) of
        Ext -> filename:rootname(File);
        _Other -> File
    end.

options(Options0) when is_list(Options0) ->
    try 
        Options = flatmap(fun(return) -> short_option(return, true);
                             (report) -> short_option(report, true);
                             ({return,T}) -> short_option(return, T);
                             ({report,T}) -> short_option(report, T);
                             (T) -> [T]
                          end, Options0),
        options(Options, [scannerfile,includefile,report_errors,
                          report_warnings,return_errors,return_warnings,
                          verbose,dfa_graph], [])
    catch error: _ -> badarg
    end;
options(Option) ->
    options([Option]).

short_option(return, T) ->
    [{return_errors,T}, {return_warnings,T}];
short_option(report, T) ->
    [{report_errors,T}, {report_warnings,T}].

options(Options0, [Key|Keys], L) when is_list(Options0) ->
    Options = case member(Key, Options0) of
                  true -> 
                      [atom_option(Key)|delete(Key, Options0)];
                  false ->
                      Options0
              end,
    V = case keysearch(Key, 1, Options) of
            {value, {Key, Filename0}} when Key =:= includefile; 
                                           Key =:= scannerfile ->
                case is_filename(Filename0) of
                    no -> 
                        badarg;
                    Filename -> 
                        {ok,[{Key,Filename}]}
                end;
            {value,{Key,Bool}} when Bool; not Bool ->
                {ok,[{Key, Bool}]};
            {value,{Key, _}} ->
                badarg;
            false ->
                {ok,[{Key,default_option(Key)}]}
        end,
    case V of
        badarg ->
            badarg;
        {ok,KeyValueL} ->
            NewOptions = keydelete(Key, 1, Options),
            options(NewOptions, Keys, KeyValueL ++ L)
    end;
options([], [], L) ->
    foldl(fun({_,false}, A) -> A;
             ({Tag,true}, A) -> [Tag|A];
             (F,A) -> [F|A]
          end, [], L);
options(_Options, _, _L) ->
    badarg.

default_option(dfa_graph) -> false;
default_option(includefile) -> [];
default_option(report_errors) -> true;
default_option(report_warnings) -> true;
default_option(return_errors) -> false;
default_option(return_warnings) -> false;
default_option(scannerfile) -> [];
default_option(verbose) -> false.

atom_option(dfa_graph) -> {dfa_graph,true};
atom_option(report_errors) -> {report_errors,true};
atom_option(report_warnings) -> {report_warnings,true};
atom_option(return_errors) -> {return_errors,true};
atom_option(return_warnings) -> {return_warnings,true};
atom_option(verbose) -> {verbose,true};
atom_option(Key) -> Key.

is_filename(T) ->
    try filename:flatten(T) of
        Filename -> Filename
    catch error: _ -> no
    end.    

shorten_filename(Name0) ->
    {ok,Cwd} = file:get_cwd(),
    case lists:prefix(Cwd, Name0) of
        false -> Name0;
        true ->
            case lists:nthtail(length(Cwd), Name0) of
                "/"++N -> N;
                N -> N
            end
    end.

leex_ret(St) ->
    report_errors(St),
    report_warnings(St),
    Es = pack_errors(St#leex.errors),
    Ws = pack_warnings(St#leex.warnings),
    if 
        Es =:= [] -> 
            case member(return_warnings, St#leex.opts) of
                true -> {ok, St#leex.efile, Ws};
                false -> {ok, St#leex.efile}
            end;
        true -> 
            case member(return_errors, St#leex.opts) of
                true -> {error, Es, Ws};
                false -> error
            end
    end.

pack_errors([{File,_} | _] = Es) ->
    [{File, flatmap(fun({_,E}) -> [E] end, sort(Es))}];
pack_errors([]) ->
    [].
    
pack_warnings([{File,_} | _] = Ws) ->
    [{File, flatmap(fun({_,W}) -> [W] end, sort(Ws))}];
pack_warnings([]) ->
    [].

report_errors(St) ->
    when_opt(fun () -> 
                     foreach(fun({File,{none,Mod,E}}) -> 
                                     io:fwrite("~s: ~s\n",
                                               [File,Mod:format_error(E)]);
                                ({File,{Line,Mod,E}}) -> 
                                     io:fwrite("~s:~w: ~s\n",
                                               [File,Line,Mod:format_error(E)])
                             end, sort(St#leex.errors))
             end, report_errors, St#leex.opts).

report_warnings(St) ->
    when_opt(fun () ->
                     foreach(fun({File,{none,Mod,W}}) -> 
                                     io:fwrite("~s: Warning: ~s\n",
                                               [File,Mod:format_error(W)]);
                                ({File,{Line,Mod,W}}) -> 
                                     io:fwrite("~s:~w: Warning: ~s\n",
                                               [File,Line,Mod:format_error(W)])
                             end, sort(St#leex.warnings))
             end, report_warnings, St#leex.opts).

add_error(E, St) ->
    add_error(St#leex.xfile, E, St).

add_error(File, Error, St) ->
    throw(St#leex{errors = [{File,Error}|St#leex.errors]}).

add_warning(Line, W, St) ->
    St#leex{warnings = [{St#leex.xfile,{Line,leex,W}}|St#leex.warnings]}.

%% filenames(File, Options, State) -> State.
%%  The default output dir is the current directory unless an
%%  explicit one has been given in the options.

filenames(File, Opts, St0) ->
    Dir = filename:dirname(File),
    Base = filename:basename(File, ".xrl"),
    Xfile = filename:join(Dir, Base ++ ".xrl"),
    Efile = Base ++ ".erl",
    Gfile = Base ++ ".dot",
    Module = list_to_atom(Base),
    St1 = St0#leex{xfile=Xfile,
                   opts=Opts,
                   module=Module},
    {value,{includefile,Ifile0}} = keysearch(includefile, 1, Opts),
    Ifile = inc_file_name(Ifile0),
    %% Test for explicit scanner file.
    {value,{scannerfile,Ofile}} = keysearch(scannerfile, 1, Opts),
    if
        Ofile =:= [] ->
            St1#leex{efile=filename:join(Dir, Efile),
                     ifile=Ifile,
                     gfile=filename:join(Dir, Gfile)};
        true ->
            D = filename:dirname(Ofile),
            St1#leex{efile=Ofile,
                     ifile=Ifile,
                     gfile=filename:join(D, Gfile)}
    end.

when_opt(Do, Opt, Opts) ->
    case member(Opt, Opts) of
        true -> Do();
        false -> ok
    end.

verbose_print(St, Format, Args) ->
    when_opt(fun () -> io:fwrite(Format, Args) end, verbose, St#leex.opts).

%% parse_file(State) -> {ok,[REA],[Action],Code,NewState} | throw(NewState)
%%  when
%%      REA = {RegExp,ActionNo};
%%      Action = {ActionNo,ActionString};
%%      Code = {StartLine, StartPos, NumOfLines}. Where the Erlang code is.
%%
%%  Read and parse the file Xfile.
%%  After each section of the file has been parsed we directly call the
%%  next section. This is done when we detect a line we don't recognise
%%  in the current section. The file format is very simple and Erlang
%%  token based, we allow empty lines and Erlang style comments.

parse_file(St0) ->
    case file:open(St0#leex.xfile, [read]) of
        {ok,Xfile} ->
            try
                verbose_print(St0, "Parsing file ~s, ", [St0#leex.xfile]),
                {ok,REAs,Actions,Code,St1} = parse_head(St0, Xfile),
                verbose_print(St1, "contained ~w rules.~n", [length(REAs)]),
                {ok,REAs,Actions,Code,St1}
            after file:close(Xfile)
            end;
        {error,Error} ->
            add_error({none,leex,{file_error,Error}}, St0)
    end.

%% parse_head(State, File)
%%  Parse the head of the file. Skip all comments and blank lines.

parse_head(St, Ifile) -> parse_defs(St, Ifile, nextline(Ifile, 0)).

%% parse_defs(State, File, Line)
%%  Parse the macro definition section of a file. This must exist.

parse_defs(St, Ifile, {ok,?DEFS_HEAD ++ Rest,L}) ->
    St1 = warn_ignored_chars(St, L, Rest),
    parse_defs(St1, Ifile, nextline(Ifile, L), []);
parse_defs(St, _, {ok,_,L}) ->
    add_error({L,leex,missing_defs}, St);
parse_defs(St, _, {eof,L}) ->
    add_error({L,leex,missing_defs}, St).

parse_defs(St, Ifile, {ok,Chars,L}, Ms) ->
    case tokens(Chars, " \t\n") of      % Also strips \n from eol!
        [Name,"=",Def] ->
            parse_defs(St, Ifile, nextline(Ifile, L), [{Name,Def}|Ms]);
        _ ->                            % Anything else
            parse_rules(St, Ifile, {ok,Chars,L}, Ms)
    end;
parse_defs(St, Ifile, Line, Ms) ->
    parse_rules(St, Ifile, Line, Ms).

%% parse_rules(State, File, Line, Macros)
%%  Parse the RE rules section of the file. This must exist.

parse_rules(St, Ifile, {ok,?RULE_HEAD ++ Rest,L}, Ms) ->
    St1 = warn_ignored_chars(St, L, Rest),
    parse_rules(St1, Ifile, nextline(Ifile, L), Ms, [], [], 0);
parse_rules(St, _, {ok,_,L}, _) ->
    add_error({L,leex,missing_rules}, St);
parse_rules(St, _, {eof,L}, _) ->
    add_error({L,leex,missing_rules}, St).

%% parse_rules(State, File, Result, Macros, RegExpActions, Actions, Acount) ->
%%      {ok,RegExpActions,Actions,Code,NewState} | throw(NewState)

parse_rules(St, Ifile, NextLine, Ms, REAs, As, N) ->
    case NextLine of
        {ok,?CODE_HEAD ++ _Rest,_} ->
            parse_rules_end(St, Ifile, NextLine, REAs, As);
        {ok,Chars,L0} ->
            %%io:fwrite("~w: ~p~n", [L0,Chars]),
            case collect_rule(Ifile, Chars, L0) of
                {ok,Re,Atoks,L1} ->
                    {ok,REA,A,St1} = parse_rule(St, Re, L0, Atoks, Ms, N),
                    parse_rules(St1, Ifile, nextline(Ifile, L1), Ms,
                                [REA|REAs], [A|As], N+1);
                {error,E} -> add_error(E, St)
            end;
        {eof,_} ->
            parse_rules_end(St, Ifile, NextLine, REAs, As)
    end.

parse_rules_end(St, _, {ok,_,L}, [], []) ->
    add_error({L,leex,empty_rules}, St);
parse_rules_end(St, _, {eof,L}, [], []) ->
    add_error({L,leex,empty_rules}, St);
parse_rules_end(St, Ifile, NextLine, REAs, As) ->
    %% Must be *VERY* careful to put rules in correct order!
    parse_code(St, Ifile, NextLine, reverse(REAs), reverse(As)).

%% collect_rule(File, Line, Lineno) ->
%%      {ok,RegExp,ActionTokens,NewLineno} | {error,E}.
%% Collect a complete rule by reading lines until the the regexp and
%% action has been read. Keep track of line number.

collect_rule(Ifile, Chars, L0) ->
    {match,St,Len} = regexp:first_match(Chars, "[^ \t\r\n]+"),
    %%io:fwrite("RE = ~p~n", [substr(Chars, St, Len)]),
    case collect_action(Ifile, substr(Chars, St+Len), L0, []) of
        {ok,[{':',_}|Toks],L1} -> {ok,substr(Chars, St, Len),Toks,L1};
        {ok,_,_} -> {error,{L0,leex,bad_rule}};
        {eof,L1} -> {error,{L1,leex,bad_rule}};
        {error,E,_} -> {error,E}
    end.

collect_action(Ifile, Chars, L0, Cont0) ->
    case erl_scan:tokens(Cont0, Chars, L0) of
        {done,{ok,Toks,_},_} -> {ok,Toks,L0};
        {done,{eof,_},_} -> {eof,L0};
        {done,{error,E,_},_} -> {error,E,L0};
        {more,Cont1} ->
            collect_action(Ifile, io:get_line(Ifile, leex), L0+1, Cont1)
    end.

%% parse_rule(State, RegExpString, RegExpLine, ActionTokens, Macros, Counter)
%%  Parse one regexp after performing macro substition.

parse_rule(St, S, Line, [{dot,_}], Ms, N) ->
    case parse_rule_regexp(S, Ms) of
        {ok,R} ->
            ok = anchors_not_yet_implemented(St, R, Line),
            {ok,{R,N},{N,empty_action},St};
        {error,E} ->
            add_error({Line,leex,{regexp,E}}, St)
    end;
parse_rule(St, S, Line, Atoks, Ms, N) ->
    case parse_rule_regexp(S, Ms) of
        {ok,R} ->
            ok = anchors_not_yet_implemented(St, R, Line),
            case erl_parse:parse_exprs(Atoks) of
                {ok,_Aes} ->
                    %% Check for token variables.
                    TokenChars = var_used('TokenChars', Atoks),
                    TokenLen = var_used('TokenLen', Atoks),
                    TokenLine = var_used('TokenLine', Atoks),
                    {ok,{R,N},{N,Atoks,TokenChars,TokenLen,TokenLine},St};
                {error,_} ->
                    add_error({Line,leex,{after_regexp,S}}, St)
            end;
        {error,E} ->
            add_error({Line,leex,{regexp,E}}, St)
    end.

anchors_not_yet_implemented(St, R, L) ->
    case catch build_nfa(R, 1, 0) of
        {'EXIT', _} ->
            add_error({L,leex,not_yet_implemented}, St);
        _ ->
            ok
    end.

var_used(Name, Toks) ->
    case keysearch(Name, 3, Toks) of
        {value,{var,_,Name}} -> true;
        _ -> false
    end.

%% parse_rule_regexp(RegExpString, Macros) -> {ok,RegExp} | {error,Error}.
%% Substitute in macros and parse RegExpString. Cannot use regexp:gsub
%% here as it uses info in replace string (&).

parse_rule_regexp(RE0, [{M,Exp}|Ms]) ->
    case regexp:matches(RE0, "{" ++ M ++ "}") of
        {match,Mats} ->
            RE1 = sub_repl(Mats, Exp, RE0, 1),
            parse_rule_regexp(RE1, Ms);
        {error,_} ->
            parse_rule_regexp(RE0, Ms)
    end;
parse_rule_regexp(RE, []) ->
    %%io:fwrite("RE = ~p~n", [RE]),
    regexp:parse(RE).

sub_repl([{St,L}|Ss], Rep, S, Pos) ->
    Rs = sub_repl(Ss, Rep, S, St+L),
    substr(S, Pos, St-Pos) ++ Rep ++ Rs;
sub_repl([], _Rep, S, Pos) -> substr(S, Pos).

%% parse_code(State, File, Line, REAs, Actions) ->
%%       {ok,RegExpActions,Actions,CodeLine,NewState}.
%%  Finds the line and the position where the code section of the file
%%  begins. This must exist.

parse_code(St, Ifile, {ok,?CODE_HEAD ++ Rest,CodeL}, REAs, As) ->
    St1 = warn_ignored_chars(St, CodeL, Rest),
    {ok, CodePos} = file:position(Ifile, cur),
    %% Just count the lines; copy the code from file to file later.
    NCodeLines = count_lines(Ifile, 0),
    {ok,REAs,As,{CodeL,CodePos,NCodeLines},St1};
parse_code(St, _, {ok,_,L}, _, _) -> 
    add_error({L,leex,missing_code}, St);
parse_code(St, _, {eof,L}, _, _) -> 
    add_error({L,leex,missing_code}, St).

count_lines(File, N) ->
    case io:get_line(File, leex) of
        eof -> N;
        _Line -> count_lines(File, N+1)
    end.

%% nextline(InputFile, PrevLineNo) -> {ok,Chars,LineNo} | {eof,LineNo}.
%%  Get the next line skipping comment lines and blank lines.

nextline(Ifile, L) ->
    case io:get_line(Ifile, leex) of
        eof -> {eof,L};
        Chars ->
            case substr(Chars, span(Chars, " \t\n")+1) of
                [$%|_Rest] -> nextline(Ifile, L+1);
                [] -> nextline(Ifile, L+1);
                _Other -> {ok,Chars,L+1}
            end
    end.

warn_ignored_chars(St, Line, S) ->
    case non_white(S) of
        [] -> St;
        _ -> add_warning(Line, ignored_characters, St)
    end.

non_white(S) ->
    [C || C <- S, C > $\s, C < $\200 orelse C > $\240].

%% We use standard methods, Thompson's construction and subset
%% construction, to create first an NFA and then a DFA from the
%% regexps. A non-standard feature is that we work with sets of
%% character ranges (crs) instead sets of characters. This is most
%% noticeable when constructing DFAs. The major benefit is that we can
%% handle characters from any set, not just limited ASCII or 8859,
%% even 16/32 bit unicode.
%%
%% The whole range of characters is 0-maxchar, where maxchar is a BIG
%% number. We don't make any assumptions about the size of maxchar, it
%% is just bigger than any character.
%%
%% Using character ranges makes describing many regexps very simple,
%% for example the regexp "." just becomes the range
%% [{0-9},{11-maxchar}].

%% make_nfa(RegExpActions) -> {ok,{NFA,StartState}} | {error,E}.
%% Build a complete nfa from a list of {RegExp,Action}. The NFA field
%% accept has values {yes,Action}|no. The NFA is a list of states.

make_dfa(REAs, St) ->
    {NFA,NF} = build_combined_nfa(REAs),
    verbose_print(St, "NFA contains ~w states, ", [tuple_size(NFA)]),
    {DFA0,DF0} = build_dfa(NFA, NF),
    verbose_print(St, "DFA contains ~w states, ", [length(DFA0)]),
    {DFA,DF} = minimise_dfa(DFA0, DF0),
    verbose_print(St, "minimised to ~w states.~n", [length(DFA)]),
    %%io:fwrite("~p\n", [{NF,NFA}]),
    %%io:fwrite("~p\n", [{DF0,DFA0}]),
    %%io:fwrite("~p\n", [{DF,DFA}]),
    {DFA,DF}.

%% build_combined_nfa(RegExpActionList) -> {NFA,FirstState}.
%%  Build the combined NFA using Thompson's construction straight out
%%  of the book. Build the separate NFAs in the same order as the
%%  rules so that the accepting have ascending states have ascending
%%  state numbers. Start numbering the states from 1 as we put the
%%  states in a tuple with the state number as the index.
%%
%%  The edges from a state are a list of {CharRange,State} | {epsilon,State}.

build_combined_nfa(REAs) ->
    {NFA0,Firsts,Free} = build_nfa_list(REAs, [], [], 1),
    F = #nfa_state{no=Free,edges=epsilon_trans(Firsts)},
    {list_to_tuple(keysort(#nfa_state.no, [F|NFA0])),Free}.

build_nfa_list([{RE,Action}|REAs], NFA0, Firsts, Free0) ->
    {NFA1,Free1,First} = build_nfa(RE, Free0, Action),
    build_nfa_list(REAs, NFA1 ++ NFA0, [First|Firsts], Free1);
build_nfa_list([], NFA, Firsts, Free) ->
    {NFA,reverse(Firsts),Free}.

epsilon_trans(Firsts) -> [ {epsilon,F} || F <- Firsts ].

%% build_nfa(RegExp, NextState, Action) -> {NFA,NextState,FirstState}.
%%  When building the NFA states for a ??? we don't build the end
%%  state, just allocate a State for it and return this state
%%  number. This allows us to avoid building unnecessary states for
%%  concatenation which would then have to be removed by overwriting
%%  an existing state.

build_nfa(RE, N0, Action) ->
    {NFA,N1,E} = build_nfa(RE, N0+1, N0, []),
    {[#nfa_state{no=E,accept={accept,Action}}|NFA],N1,N0}.

%% build_nfa(RegExp, NextState, FirstState, NFA) -> {NFA,NextState,EndState}.
%%  The NFA is a list of nfa_state is no predefined order. The state
%%  number of the returned EndState is already allocated!

build_nfa({'or',RE1,RE2}, N0, F, NFA0) ->
    {NFA1,N1,E1} = build_nfa(RE1, N0+1, N0, NFA0),
    {NFA2,N2,E2} = build_nfa(RE2, N1+1, N1, NFA1),
    E = N2,                             % End state
    {[#nfa_state{no=F,edges=[{epsilon,N0},{epsilon,N1}]},
      #nfa_state{no=E1,edges=[{epsilon,E}]},
      #nfa_state{no=E2,edges=[{epsilon,E}]}|NFA2],
     N2+1,E};
build_nfa({concat,RE1, RE2}, N0, F, NFA0) ->
    {NFA1,N1,E1} = build_nfa(RE1, N0, F, NFA0),
    {NFA2,N2,E2} = build_nfa(RE2, N1, E1, NFA1),
    {NFA2,N2,E2};
build_nfa({kclosure,RE}, N0, F, NFA0) ->
    {NFA1,N1,E1} = build_nfa(RE, N0+1, N0, NFA0),
    E = N1,                             % End state
    {[#nfa_state{no=F,edges=[{epsilon,N0},{epsilon,E}]},
      #nfa_state{no=E1,edges=[{epsilon,N0},{epsilon,E}]}|NFA1],
     N1+1,E};
build_nfa({pclosure,RE}, N0, F, NFA0) ->
    {NFA1,N1,E1} = build_nfa(RE, N0+1, N0, NFA0),
    E = N1,                             % End state
    {[#nfa_state{no=F,edges=[{epsilon,N0}]},
      #nfa_state{no=E1,edges=[{epsilon,N0},{epsilon,E}]}|NFA1],
     N1+1,E};
build_nfa({optional,RE}, N0, F, NFA0) ->
    {NFA1,N1,E1} = build_nfa(RE, N0+1, N0, NFA0),
    E = N1,                             % End state
    {[#nfa_state{no=F,edges=[{epsilon,N0},{epsilon,E}]},
      #nfa_state{no=E1,edges=[{epsilon,E}]}|NFA1],
     N1+1,E};
build_nfa({char_class,Cc}, N, F, NFA) ->
    {[#nfa_state{no=F,edges=[{char_class(Cc),N}]}|NFA],N+1,N};
build_nfa({comp_class,Cc}, N, F, NFA) ->
    {[#nfa_state{no=F,edges=[{comp_class(Cc),N}]}|NFA],N+1,N};
build_nfa(C, N, F, NFA) when is_integer(C) ->
    {[#nfa_state{no=F,edges=[{[{C,C}],N}]}|NFA],N+1,N}.

char_class(Cc) ->
    Crs = lists:foldl(fun ({C1,C2}, Set) -> add_element({C1,C2}, Set);
                          (C, Set) -> add_element({C,C}, Set)
                      end, ordsets:new(), Cc),
    pack_crs(ordsets:to_list(Crs)).

pack_crs([{C1,C2}=Cr,{C3,C4}|Crs]) when C1 =< C3, C2 >= C4 ->
    %% C1      C2
    %%   C3  C4
    pack_crs([Cr|Crs]);
pack_crs([{C1,C2},{C3,C4}|Crs]) when C2 >= C3, C2 < C4 ->
    %% C1    C2
    %%    C3   C4
    pack_crs([{C1,C4}|Crs]);
pack_crs([{C1,C2},{C3,C4}|Crs]) when C2 + 1 == C3 ->
    %% C1   C2
    %%        C3  C4
    pack_crs([{C1,C4}|Crs]);
pack_crs([Cr|Crs]) -> [Cr|pack_crs(Crs)];
pack_crs([]) -> [].

comp_class(Cc) ->
    Crs = char_class(Cc),
    %%io:fwrite("comp: ~p\n", [Crs]),
    comp_crs(Crs, 0).

comp_crs([{C1,C2}|Crs], Last) ->
    [{Last,C1-1}|comp_crs(Crs, C2+1)];
comp_crs([], Last) -> [{Last,maxchar}].

%% build_dfa(NFA, NfaFirstState) -> {DFA,DfaFirstState}.
%%  Build a DFA from an NFA using "subset construction". The major
%%  difference from the book is that we keep the marked and unmarked
%%  DFA states in seperate lists. New DFA states are added to the
%%  unmarked list and states are marked by moving them to the marked
%%  list. We assume that the NFA accepting state numbers are in
%%  ascending order for the rules and use ordsets to keep this order.

build_dfa(NFA, Nf) ->
    D = #dfa_state{no=0,nfa=eclosure([Nf], NFA)},
    {build_dfa([D], 1, [], NFA),0}.

%% build_dfa([UnMarked], NextState, [Marked], NFA) -> DFA.
%%  Traverse the unmarked states. Temporarily add the current unmarked
%%  state to the marked list before calculating translation, this is
%%  to avoid adding too many duplicate states. Add it properly to the
%%  marked list afterwards with correct translations.

build_dfa([U|Us0], N0, Ms, NFA) ->
    {Ts,Us1,N1} = build_dfa(U#dfa_state.nfa, Us0, N0, [], [U|Ms], NFA),
    M = U#dfa_state{trans=Ts,accept=accept(U#dfa_state.nfa, NFA)},
    build_dfa(Us1, N1, [M|Ms], NFA);
build_dfa([], _, Ms, _) -> Ms.

%% build_dfa([NfaState], [Unmarked], NextState, [Transition], [Marked], NFA) ->
%%      {Transitions,UnmarkedStates,NextState}.
%%  Foreach NFA state set calculate the legal translations. N.B. must
%%  search *BOTH* the unmarked and marked lists to check if DFA state
%%  already exists. As the range of characters is potentially VERY
%%  large we cannot explicitly test all characters. Instead we first
%%  calculate the set of all disjoint character ranges which are
%%  possible candidates to the set of NFA states. The transitions are
%%  an orddict so we get the transition lists in ascending order.

build_dfa(Set, Us, N, Ts, Ms, NFA) ->
    %% List of all transition sets.
    Crs0 = [Cr || S <- Set,
                  {Crs,_St} <- (element(S, NFA))#nfa_state.edges,
                  Crs /= epsilon,        % Not an epsilon transition
                  Cr <- Crs ],
    Crs1 = lists:usort(Crs0),            % Must remove duplicates!
    %% Build list of disjoint test ranges.
    Test = disjoint_crs(Crs1),
    %%io:fwrite("bd: ~p\n    ~p\n    ~p\n    ~p\n", [Set,Crs0,Crs1,Test]),
    build_dfa(Test, Set, Us, N, Ts, Ms, NFA).

%% disjoint_crs([CharRange]) -> [CharRange].
%%  Take a sorted list of char ranges and make a sorted list of
%%  disjoint char ranges. No new char range extends past an existing
%%  char range.

disjoint_crs([{_C1,C2}=Cr1,{C3,_C4}=Cr2|Crs]) when C2 < C3 ->
    %% C1  C2
    %%        C3  C4
    [Cr1|disjoint_crs([Cr2|Crs])];
disjoint_crs([{C1,C2},{C3,C4}|Crs]) when C1 == C3 ->
    %% C1     C2
    %% C3       C4
    [{C1,C2}|disjoint_crs(add_element({C2+1,C4}, Crs))];
disjoint_crs([{C1,C2},{C3,C4}|Crs]) when C1 < C3, C2 >= C3, C2 < C4 ->
    %% C1     C2
    %%    C3     C4
    [{C1,C3-1}|disjoint_crs(union([{C3,C2},{C2+1,C4}], Crs))];
disjoint_crs([{C1,C2},{C3,C4}|Crs]) when C1 < C3, C2 == C4 ->
    %% C1      C2
    %%    C3   C4
    [{C1,C3-1}|disjoint_crs(add_element({C3,C4}, Crs))];
disjoint_crs([{C1,C2},{C3,C4}|Crs]) when C1 < C3, C2 > C4 ->
    %% C1        C2
    %%    C3   C4
    [{C1,C3-1}|disjoint_crs(union([{C3,C4},{C4+1,C2}], Crs))];
disjoint_crs([Cr|Crs]) -> [Cr|disjoint_crs(Crs)];
disjoint_crs([]) -> [].

build_dfa([Cr|Crs], Set, Us, N, Ts, Ms, NFA) ->
    case eclosure(move(Set, Cr, NFA), NFA) of
        S when S /= [] ->
            case dfa_state_exist(S, Us, Ms) of
                {yes,T} ->
                    build_dfa(Crs, Set, Us, N, store(Cr, T, Ts), Ms, NFA);
                no ->
                    U = #dfa_state{no=N,nfa=S},
                    build_dfa(Crs, Set, [U|Us], N+1, store(Cr, N, Ts), Ms, NFA)
            end;
        [] ->
            build_dfa(Crs, Set, Us, N, Ts, Ms, NFA)
    end;
build_dfa([], _, Us, N, Ts, _, _) ->
    {Ts,Us,N}.

%% dfa_state_exist(Set, Unmarked, Marked) -> {yes,State} | no.

dfa_state_exist(S, Us, Ms) ->
    case keysearch(S, #dfa_state.nfa, Us) of
        {value,#dfa_state{no=T}} -> {yes,T};
        false ->
            case keysearch(S, #dfa_state.nfa, Ms) of
                {value,#dfa_state{no=T}} -> {yes,T};
                false -> no
            end
    end.

%% eclosure([State], NFA) -> [State].
%% move([State], Char, NFA) -> [State].
%%  These are straight out of the book. As eclosure uses ordsets then
%%  the generated state sets are in ascending order.

eclosure(Sts, NFA) -> eclosure(Sts, NFA, []).

eclosure([St|Sts], NFA, Ec) ->
    #nfa_state{edges=Es} = element(St, NFA),
    eclosure([ N || {epsilon,N} <- Es,
                    not is_element(N, Ec) ] ++ Sts,
             NFA, add_element(St, Ec));
eclosure([], _, Ec) -> Ec.

move(Sts, Cr, NFA) ->
    %% io:fwrite("move1: ~p\n", [{Sts,Cr}]),
    [ St || N <- Sts,
            {Crs,St} <- (element(N, NFA))#nfa_state.edges,
            Crs /= epsilon,             % Not an epsilon transition
            in_crs(Cr, Crs) ].

in_crs({C1,C2}, [{C3,C4}|_Crs]) when C1 >= C3, C2 =< C4 -> true;
in_crs(Cr, [Cr|_Crs]) -> true;          % Catch bos and eos.
in_crs(Cr, [_|Crs]) -> in_crs(Cr, Crs);
in_crs(_Cr, []) -> false.

%% accept([State], NFA) -> {accept,A} | noaccept.
%%  Scan down the state list until we find an accepting state.

accept([St|Sts], NFA) ->
    case element(St, NFA) of
        #nfa_state{accept={accept,A}} -> {accept,A};
        #nfa_state{accept=noaccept} -> accept(Sts, NFA)
    end;
accept([], _) -> noaccept.

%% minimise_dfa(DFA, DfaFirst) -> {DFA,DfaFirst}.
%%  Minimise the DFA by removing equivalent states. We consider a
%%  state if both the transitions and the their accept state is the
%%  same.  First repeatedly run throught the DFA state list removing
%%  equivalent states and updating remaining transitions with
%%  remaining equivalent state numbers. When no more reductions are
%%  possible then pack the remaining state numbers to get consecutive
%%  states.

minimise_dfa(DFA0, Df0) ->
    case min_dfa(DFA0) of
        {DFA1,[]} ->                    % No reduction!
            {DFA2,Rs} = pack_dfa(DFA1),
            {min_update(DFA2, Rs),min_use(Df0, Rs)};
        {DFA1,Rs} ->
            minimise_dfa(min_update(DFA1, Rs), min_use(Df0, Rs))
    end.

min_dfa(DFA) -> min_dfa(DFA, [], []).

min_dfa([D|DFA0], Rs0, MDFA) ->
    {DFA1,Rs1} = min_delete(DFA0, D#dfa_state.trans, D#dfa_state.accept,
                            D#dfa_state.no, Rs0, []),
    min_dfa(DFA1, Rs1, [D|MDFA]);
min_dfa([], Rs, MDFA) -> {MDFA,Rs}.

%% min_delete(States, Trans, Action, NewN, Rs, MiniDFA) -> {MiniDFA,Rs}.
%%  Delete all states with same transactions and action. Return
%%  rewrites and minimised DFA with no duplicate states.

min_delete([#dfa_state{no=N,trans=T,accept=A}|DFA], T, A, NewN, Rs, MDFA) ->
    min_delete(DFA, T, A, NewN, [{N,NewN}|Rs], MDFA);
min_delete([D|DFA], T, A, NewN, Rs, MDFA) ->
    min_delete(DFA, T, A, NewN, Rs, [D|MDFA]);
min_delete([], _, _, _, Rs, MDFA) -> {MDFA,Rs}.

min_update(DFA, Rs) ->
    [ D#dfa_state{trans=min_update_trans(D#dfa_state.trans, Rs)} || D <- DFA ].

min_update_trans(Tr, Rs) ->
    [ {C,min_use(S, Rs)} || {C,S} <- Tr ].

min_use(Old, [{Old,New}|_]) -> New;
min_use(Old, [_|Reds]) -> min_use(Old, Reds);
min_use(Old, []) -> Old.

pack_dfa(DFA) -> pack_dfa(DFA, 0, [], []).

pack_dfa([D|DFA], NewN, Rs, PDFA) ->
    pack_dfa(DFA, NewN+1,
             [{D#dfa_state.no,NewN}|Rs], [D#dfa_state{no=NewN}|PDFA]);
pack_dfa([], _, Rs, PDFA) -> {PDFA,Rs}.

%% The main output is the yystate function which is built from the
%% DFA. It has the spec:
%%
%% yystate() -> InitialState.
%% yystate(State, InChars, Line, CurrTokLen, AcceptAction, AcceptLen) ->
%%      {Action, AcceptLength, RestChars, Line} |         Accepting end state
%%      {Action, AcceptLength, RestChars, Line, State} |  Accepting state
%%      {reject, AcceptLength, CurrTokLen, RestChars, Line, State} |
%%      {Action, AcceptLength, CurrTokLen, RestChars, Line, State}.

%% The return CurrTokLen is always the current number of characters
%% scanned in the current token. The returns have the follwoing
%% meanings:
%% {Action, AcceptLength, RestChars, Line} -
%%  The scanner has reached an accepting end-state, for example after
%%  a regexp "abc". Action is the action number and AcceptLength is
%%  the length of the matching token.
%%
%% {Action, AcceptLength, RestChars, Line, State} -
%%  The scanner has reached an accepting transition state, for example
%%  after c in regexp "abc(xyz)?", continuation depends on
%%  RestChars. If RestChars == [] (no more current characters) then we
%%  need to get more characters to see if it is an end-state,
%%  otherwise (eof or chars) then we have not found continuing
%%  characters and it is an end state.
%%
%% {reject, AcceptLength, CurrTokLen, RestChars, Line, State} -
%% {Action, AcceptLength, CurrTokLen, RestChars, Line, State} -
%%  The scanner has reached a non-accepting transistion state. If
%%  RestChars == [] we need to get more characters to continue.
%%  Otherwise if 'reject' then no accepting state has been reached it
%%  is an error. If we have an Action and AcceptLength then these are
%%  the last accept state, use them and continue from there.

%% out_file(LeexState, DFA, DfaStart, [Action], Code) -> ok | error.
%%  Generate an output .erl file from the include file, the DFA and
%%  the code for the actions.

out_file(St0, DFA, DF, Actions, Code) ->
    verbose_print(St0, "Writing file ~s, ", [St0#leex.efile]),
    case open_inc_file(St0) of
        {ok,Ifile} ->
            try
                case file:open(St0#leex.efile, [write]) of
                    {ok,Ofile} ->
                        try 
                            output_file_directive(Ofile, St0#leex.ifile, 0),
                            out_file(Ifile, Ofile, St0, DFA, DF, Actions,
                                     Code, 1),
                            verbose_print(St0, "ok~n", []),
                            St0
                        after file:close(Ofile)
                        end;
                    {error,Error} ->
                        verbose_print(St0, "not ok~n", []),
                        add_error({none,leex,{file_error,Error}}, St0)
                end
            after file:close(Ifile)
            end;
        {{error,Error},Ifile} ->
            add_error(Ifile, {none,leex,{file_error,Error}}, St0)
    end.

open_inc_file(State) ->
    Ifile = State#leex.ifile,
    case file:open(Ifile, [read]) of
        {ok,F} -> {ok,F};
        Error -> {Error,Ifile}
    end.

inc_file_name([]) ->
    Incdir = filename:join(code:lib_dir(parsetools), "include"),
    filename:join(Incdir, ?LEEXINC);
inc_file_name(Filename) ->
    Filename.
                    
%% out_file(IncFile, OutFile, State, DFA, DfaStart, Actions, Code, Line) -> ok
%%  Copy the include file line by line substituting special lines with
%%  generated code. We cheat by only looking at the first 5
%%  characters.

out_file(Ifile, Ofile, St, DFA, DF, Actions, Code, L) ->
    case io:get_line(Ifile, leex) of
        eof -> output_file_directive(Ofile, St#leex.ifile, L);
        Line ->
            case substr(Line, 1, 5) of
                "##mod" -> out_module(Ofile, St);
                "##cod" -> out_erlang_code(Ofile, St, Code, L);
                "##dfa" -> out_dfa(Ofile, St, DFA, Code, DF, L);
                "##act" -> out_actions(Ofile, St#leex.xfile, Actions);
                _ -> io:put_chars(Ofile, Line)
            end,
            out_file(Ifile, Ofile, St, DFA, DF, Actions, Code, L+1)
    end.

out_module(File, St) ->
    io:fwrite(File, "-module(~w).\n", [St#leex.module]).

out_erlang_code(File, St, Code, L) ->
    {CodeL,CodePos,_NCodeLines} = Code,
    output_file_directive(File, St#leex.xfile, CodeL),
    {ok,Xfile} = file:open(St#leex.xfile, [read]),
    try
        {ok,_} = file:position(Xfile, CodePos),
        {ok,_} = file:copy(Xfile, File)
    after 
        file:close(Xfile)
    end,
    io:nl(File),
    output_file_directive(File, St#leex.ifile, L).

out_dfa(File, St, DFA, Code, DF, L) ->
    {_CodeL,_CodePos,NCodeLines} = Code,
    %% Three file attributes before this one...
    output_file_directive(File, St#leex.efile, L+(NCodeLines-1)+3),
    io:fwrite(File, "yystate() -> ~w.~n~n", [DF]),
    foreach(fun (S) -> out_trans(File, S) end, DFA),
    io:fwrite(File, "yystate(S, Ics, Line, Tlen, Action, Alen) ->~n", []),
    io:fwrite(File, "    {Action,Alen,Tlen,Ics,Line,S}.~n", []).

out_trans(File, #dfa_state{no=N,trans=[],accept={accept,A}}) ->
    %% Accepting end state, guaranteed done.
    io:fwrite(File, "yystate(~w, Ics, Line, Tlen, _, _) ->~n", [N]),
    io:fwrite(File, "    {~w,Tlen,Ics,Line};~n", [A]);
out_trans(File, #dfa_state{no=N,trans=Tr,accept={accept,A}}) ->
    %% Accepting state, but there maybe more.
    foreach(fun (T) -> out_accept_tran(File, N, A, T) end, pack_trans(Tr)),
    io:fwrite(File, "yystate(~w, Ics, Line, Tlen, _, _) ->~n", [N]),
    io:fwrite(File, "    {~w,Tlen,Ics,Line,~w};~n", [A,N]);
out_trans(File, #dfa_state{no=N,trans=Tr,accept=noaccept}) ->
    %% Non-accepting transition state.
    foreach(fun (T) -> out_noaccept_tran(File, N, T) end, pack_trans(Tr)),
    io:fwrite(File, "yystate(~w, Ics, Line, Tlen, Action, Alen) ->~n", [N]),
    io:fwrite(File, "    {Action,Alen,Tlen,Ics,Line,~w};~n", [N]).

out_accept_tran(File, N, A, {{Cf,maxchar},S}) ->
    out_accept_head_max(File, N, Cf),
    out_accept_body(File, S, "Line", A);
out_accept_tran(File, N, A, {{Cf,Cl},S}) ->
    out_accept_head_range(File, N, Cf, Cl),
    out_accept_body(File, S, "Line", A);
out_accept_tran(File, N, A, {$\n,S}) ->
    out_accept_head_1(File, N, $\n),
    out_accept_body(File, S, "Line+1", A);
out_accept_tran(File, N, A, {C,S}) ->
    out_accept_head_1(File, N, C),
    out_accept_body(File, S, "Line", A).

out_accept_head_1(File, State, Char) ->
    out_head_1(File, State, Char, "_", "_").

out_accept_head_max(File, State, Min) ->
    out_head_max(File, State, Min, "_", "_").

out_accept_head_range(File, State, Min, Max) ->
    out_head_range(File, State, Min, Max, "_", "_").

out_accept_body(File, Next, Line, Action) ->
    out_body(File, Next, Line, io_lib:write(Action), "Tlen").

out_noaccept_tran(File, N, {{Cf,maxchar},S}) ->
    out_noaccept_head_max(File, N, Cf),
    out_noaccept_body(File, S, "Line");
out_noaccept_tran(File, N, {{Cf,Cl},S}) ->
    out_noaccept_head_range(File, N, Cf, Cl),
    out_noaccept_body(File, S, "Line");
out_noaccept_tran(File, N, {$\n,S}) ->
    out_noaccept_head_1(File, N, $\n),
    out_noaccept_body(File, S, "Line+1");
out_noaccept_tran(File, N, {C,S}) ->
    out_noaccept_head_1(File, N, C),
    out_noaccept_body(File, S, "Line").

out_noaccept_head_1(File, State, Char) ->
    out_head_1(File, State, Char, "Action", "Alen").

out_noaccept_head_max(File, State, Min) ->
    out_head_max(File, State, Min, "Action", "Alen").

out_noaccept_head_range(File, State, Min, Max) ->
    out_head_range(File, State, Min, Max, "Action", "Alen").

out_noaccept_body(File, Next, Line) ->
    out_body(File, Next, Line, "Action", "Alen").

out_head_1(File, State, Char, Action, Alen) ->
    io:fwrite(File, "yystate(~w, [~w|Ics], Line, Tlen, ~s, ~s) ->\n",
              [State,Char,Action,Alen]).

out_head_max(File, State, Min, Action, Alen) ->
    io:fwrite(File, "yystate(~w, [C|Ics], Line, Tlen, ~s, ~s) when C >= ~w ->\n",
              [State,Action,Alen,Min]).

out_head_range(File, State, Min, Max, Action, Alen) ->
    io:fwrite(File, "yystate(~w, [C|Ics], Line, Tlen, ~s, ~s) when C >= ~w, C =< ~w ->\n",
              [State,Action,Alen,Min,Max]).

out_body(File, Next, Line, Action, Alen) ->
    io:fwrite(File, "    yystate(~w, Ics, ~s, Tlen+1, ~s, ~s);\n",
              [Next,Line,Action,Alen]).

%% pack_trans([{Crange,State}]) -> [{Crange,State}] when
%%      Crange = {Char,Char} | Char.
%%  Pack the translation table into something more suitable for
%%  generating code. We KNOW how the pattern matching compiler works
%%  so solitary characters are stored before ranges. We do this by
%%  prepending singletons to the front of the packed transitions and
%%  appending ranges to the back. This preserves the smallest to
%%  largest order of ranges. Newline characters, $\n, are always
%%  extracted and handled as singeltons.

pack_trans(Trs) -> pack_trans(Trs, []).

%% pack_trans(Trs) ->
%%     Trs1 = pack_trans(Trs, []),
%%     io:fwrite("tr:~p\n=> ~p\n", [Trs,Trs1]),
%%     Trs1.

pack_trans([{{C,C},S}|Trs], Pt) ->         % Singletons to the head
    pack_trans(Trs, [{C,S}|Pt]);
%% Special detection and handling of $\n.
pack_trans([{{Cf,$\n},S}|Trs], Pt) ->
    pack_trans([{{Cf,$\n-1},S}|Trs], [{$\n,S}|Pt]);
pack_trans([{{$\n,Cl},S}|Trs], Pt) ->
    pack_trans([{{$\n+1,Cl},S}|Trs], [{$\n,S}|Pt]);
pack_trans([{{Cf,Cl},S}|Trs], Pt) when Cf < $\n, Cl > $\n ->
    pack_trans([{{Cf,$\n-1},S},{{$\n+1,Cl},S}|Trs], [{$\n,S}|Pt]);
%% Small ranges become singletons.
pack_trans([{{Cf,Cl},S}|Trs], Pt) when Cl == Cf + 1 ->
    pack_trans(Trs, [{Cf,S},{Cl,S}|Pt]);
pack_trans([Tr|Trs], Pt) ->                % The default uninteresting case
    pack_trans(Trs, Pt ++ [Tr]);
pack_trans([], Pt) -> Pt.

%% out_actions(File, XrlFile, ActionList) -> ok.
%% Write out the action table.

out_actions(File, XrlFile, As) ->
    As1 = prep_out_actions(As),
    foreach(fun (A) -> out_action(File, A) end, As1),
    io:fwrite(File, "yyaction(_, _, _, _) -> error.~n", []),
    foreach(fun (A) -> out_action_code(File, XrlFile, A) end, As1).

prep_out_actions(As) ->
    map(fun ({A,empty_action}) ->
                {A,empty_action};
            ({A,Code,TokenChars,TokenLen,TokenLine}) ->
                Vs = [{"TokenChars",TokenChars},
                      {"TokenLen",TokenLen},
                      {"TokenLine",TokenLine},
                      {"YYtcs",TokenChars},
                      {"TokenLen",TokenLen or TokenChars}],
                Vars = [if F -> S; true -> "_" end || {S,F} <- Vs],
                Name = list_to_atom(lists:concat([yy_,A,'_'])),
                [Chars,Len,Line,_,_] = Vars,
                Args = [V || V <- [Chars,Len,Line], V =/= "_"],
                ArgsChars = string:join(Args, ", "),
                {A,Code,Vars,Name,Args,ArgsChars}
        end, As).

out_action(File, {A,empty_action}) ->
    io:fwrite(File, "yyaction(~w, _, _, _) -> skip_token;~n", [A]);
out_action(File, {A,_Code,Vars,Name,_Args,ArgsChars}) ->
    [_,_,Line,Tcs,Len] = Vars,
    io:fwrite(File, "yyaction(~w, ~s, ~s, ~s) ->~n", [A,Len,Tcs,Line]),
    if
        Tcs =/= "_" ->
            io:fwrite(File, "    TokenChars = yypre(YYtcs, TokenLen),~n", []);
        true -> ok
    end,
    io:fwrite(File, "    ~s(~s);~n", [Name, ArgsChars]).

out_action_code(_File, _XrlFile, {_A,empty_action}) ->
    ok;
out_action_code(File, XrlFile, {_A,Code,_Vars,Name,Args,ArgsChars}) ->
    %% Should set the file to the .erl file, but instead assumes that
    %% ?LEEXINC is syntactically correct.
    io:fwrite(File, "\n-compile({inline,~w/~w}).\n", [Name, length(Args)]),
    {line, L} = erl_scan:token_info(hd(Code), line),
    output_file_directive(File, XrlFile, L-2),
    io:fwrite(File, "~s(~s) ->~n", [Name, ArgsChars]),
    io:fwrite(File, "    ~s.\n", [pp_tokens(Code, L)]).

%% Keeps the line breaks of the original code.
pp_tokens(Tokens, Line0) ->
    lists:concat(pp_tokens1(Tokens, Line0, [])).
    
pp_tokens1([], _Line0, _T0) ->
    [];
pp_tokens1([T | Ts], Line0, T0) ->
    {line, Line} = erl_scan:token_info(T, line),
    [pp_sep(Line, Line0, T0), pp_symbol(T) | pp_tokens1(Ts, Line, T)].

pp_symbol({var,_,Var}) -> Var;
pp_symbol({_,_,Symbol}) -> io_lib:fwrite("~p", [Symbol]);
pp_symbol({dot, _}) -> "";
pp_symbol({Symbol, _}) -> Symbol.

pp_sep(Line, Line0, T0) when Line > Line0 -> 
    ["\n    " | pp_sep(Line - 1, Line0, T0)];
pp_sep(_Line, _Line0, {'.',_}) -> 
    "";
pp_sep(_Line, _Line0, _T0) -> 
    " ".

%% out_dfa_graph(LeexState, DFA, DfaStart) -> ok | error.
%%  Writes the DFA to a .dot file in DOT-format which can be viewed
%%  with Graphviz.

out_dfa_graph(St, DFA, DF) ->
    verbose_print(St, "Writing DFA to file ~s, ", [St#leex.gfile]),
    case file:open(St#leex.gfile, [write]) of
        {ok,Gfile} ->
            try
                io:fwrite(Gfile, "digraph DFA {~n", []),
                out_dfa_states(Gfile, DFA, DF),
                out_dfa_edges(Gfile, DFA),
                io:fwrite(Gfile, "}~n", []),
                verbose_print(St, "ok~n", []),
                St
            after file:close(Gfile)
            end;
        {error,Error} ->
            verbose_print(St, "not ok~n", []),
            add_error({none,leex,{file_error,Error}}, St)
    end.

out_dfa_states(File, DFA, DF) ->
    foreach(fun (S) -> out_dfa_state(File, DF, S) end, DFA),
    io:fwrite(File, "~n", []).

out_dfa_state(File, DF, #dfa_state{no=DF, accept={accept,_}}) ->
    io:fwrite(File, "  ~b [shape=doublecircle color=green];~n", [DF]);
out_dfa_state(File, DF, #dfa_state{no=DF, accept=noaccept}) ->
    io:fwrite(File, "  ~b [shape=circle color=green];~n", [DF]);
out_dfa_state(File, _, #dfa_state{no=S, accept={accept,_}}) ->
    io:fwrite(File, "  ~b [shape=doublecircle];~n", [S]);    
out_dfa_state(File, _, #dfa_state{no=S, accept=noaccept}) ->
    io:fwrite(File, "  ~b [shape=circle];~n", [S]).

out_dfa_edges(File, DFA) ->
    foreach(fun (#dfa_state{no=S,trans=Trans}) ->
                    Pt = pack_trans(Trans),
                    Tdict = foldl(fun ({Cr,T}, D) ->
                                          orddict:append(T, Cr, D)
                                  end, orddict:new(), Pt),
                    foreach(fun (T) ->
                                    Crs = orddict:fetch(T, Tdict),
                                    Edgelab = dfa_edgelabel(Crs),
                                    io:fwrite(File, "  ~b -> ~b [label=\"~s\"];~n",
                                              [S,T,Edgelab])
                            end, sort(orddict:fetch_keys(Tdict)))
            end, DFA).

dfa_edgelabel([C]) when is_integer(C) -> quote(C);
dfa_edgelabel(Cranges) ->
    "[" ++ map(fun ({A,B}) -> [quote(A), "-", quote(B)];
                   (C)     -> [quote(C)]
               end, Cranges) ++ "]".

output_file_directive(File, Filename, Line) ->
    io:fwrite(File, <<"-file(~s, ~w).\n">>, 
              [format_filename(Filename), Line]).

format_filename(Filename) ->
    io_lib:write_string(filename:flatten(Filename)).

quote($^)  -> "\\^";
quote($.)  -> "\\.";
quote($$)  -> "\\$";
quote($-)  -> "\\-";
quote($[)  -> "\\[";
quote($])  -> "\\]";
quote($\s) -> "\\\\s";
quote($\") -> "\\\"";
quote($\b) -> "\\\\b";
quote($\f) -> "\\\\f";
quote($\n) -> "\\\\n";
quote($\r) -> "\\\\r";
quote($\t) -> "\\\\t";
quote($\e) -> "\\\\e";
quote($\v) -> "\\\\v";
quote($\d) -> "\\\\d";
quote($\\) -> "\\\\";
quote(C) when 32 =< C, C =< 126 -> [C];
quote(C) when 0 =< C, C =< 255 ->
    <<T2:2,T1:3,T0:3>> = <<C>>,
    ["\\\\", $0+T2, $0+T1, $0+T0];
quote(maxchar) ->
    "MAX".
