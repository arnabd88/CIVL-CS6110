/**
* This file defines the syntax of CIVL's command line specification.
* There are totally 7 commands, namely, compare, gui, help, replay, run, show, and verify.
* There are a number of options to be chosen as well.
*  
* The usage of the commands are as follows:
* civl compare [option]* -spec [option]* file+ -impl [option]* file+
* civl gui (no options needed)
* civl help [command]
* civl replay [option]* file+ (replay for one program)
* civl replay [option]* -spec [option]* file+ -impl [option]* file+ 
* (replay for the comparison of two programs.)
* civl run [option]* file+
* civl show [option]* file+
* civl verify [option]* file+
*/
grammar Command;

/* The top-level rule */
start
    :
      'help' (REPLAY | COMMAND | 'help')? NEWLINE # help
    | 'compare' commonOption? specOrImplCommand NEWLINE #compare
    | (REPLAY | COMMAND) commandBody NEWLINE #normal
    | REPLAY commonOption? specOrImplCommand NEWLINE #replayCompare
    ;

specOrImplCommand
    : specCommand implCommand
    | implCommand specCommand
    ;
    
commonOption
    :
    option+
    ;

specCommand
    :
    SPEC commandBody
    ;

implCommand
    :
    IMPL commandBody 
    ;
    
commandBody
    :
    option* file+
    ;

option
    :
      OPTION_NAME ('=' value )? # normalOption
    | INPUT VAR '=' value   # inputOption
    | MACRO VAR ('=' value)? # macroOption
    ;

file
    :
    PATH
    ;

value
    : BOOLEAN
    | VAR
    | NUMBER
    | PATH
    ;

BOOLEAN
    : 'true' | 'false'
    ;

NUMBER
    :
    [\-\+]?[0-9]+
    ;

SPEC
    :'-spec'
    ;
    
IMPL
    :'-impl'
    ;

INPUT
    : '-input'
    ;

MACRO
    : '-D'
    ;

COMMAND:
    'verify' | 'run' | 'show' | 'gui'
    ;

REPLAY
    :
    'replay'
    ;

OPTION_NAME
    :
      '-ast'
    | '-collectHeaps'
    | '-collectProcesses'
    | '-collectScopes'
    | '-deadlock'
    | '-debug'
    | '-echo'
    | '-enablePrintf'
    | '-errorBound'
    | '-gui'
    | '-guided'
    | '-id'
    | '-maxdepth'
    | '-min'
    | '-ompNoSimplify'
    | '-preproc'
    | '-random'
    | '-saveStates'
    | '-seed'
    | '-showAmpleSet'
    | '-showAmpleSetWtStates'
    | '-showInputs'
    | '-showModel'
    | '-showPathCondition'
    | '-showProgram'
    | '-showProverQueries'
    | '-showQueries'
    | '-showSavedStates'
    | '-showStates'
    | '-showTime'
    | '-showTransitions'
    | '-simplify'
    | '-solve'
    | '-statelessPrintf'
    | '-svcomp'
    | '-sysIncludePath'
    | '-trace'
    | '-userIncludePath'
    | '-verbose'
    | '-web'
    ;

VAR
    :
    [_a-zA-Z] [_a-zA-Z0-9]*
    ;

PATH
    :
    ([_a-zA-Z0-9\.\/])([_a-zA-Z0-9\-\.\/])*
    ;

NEWLINE
    : '\r'? '\n'
    ;

/*STRING
    : ~[ =\-\r\n\t]+;*/

WS
    : [ \t]+ -> skip
    ;
