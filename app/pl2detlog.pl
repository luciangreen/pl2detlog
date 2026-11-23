/*  pl2detlog.pl -- the command line of the SWI-Prolog module pl2detlog

    Installed as a pack:   swipl pl2detlog compile prog.pl -g main
    From a clone:          swipl app/pl2detlog.pl compile prog.pl -g main
*/

:- initialization(main, main).

:- (   prolog_load_context(directory, D),
       atomic_list_concat([D, '/../prolog/pl2detlog.pl'], F),
       exists_file(F)
   ->  use_module(F)
   ;   use_module(library(pl2detlog))
   ).

main(Argv) :-
    catch(pl2detlog_cli(Argv), E, ( print_message(error, E), halt(1) )).
