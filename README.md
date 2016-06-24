This directory contains the prototype implementation of the static
analysis described in the paper

    A Parametric Abstract Domain for Lattice-Valued Regular Expressions
    Jan Midtgaard, Flemming Nielson, and Hanne Riis Nielson
    SAS 2016

The prototype supports a slightly larger language than described in
the paper.  In particular, the supported Boolean expressions are:

    b ::= tt | ff | neg b | a0 = a1 | a0 < a1 | a0 <= a1

The supported core language is available in ast.ml as the type 'prog'.

A slightly extended language is available as 'exprog' along with a
desugarer ('desugar_proc' and 'desugar_twoproc') for translating the
extended language back to the core language.  Furthermore the
prototype includes a parser for the extended language.


Requirements:
-------------

To build the prototype and try the examples you need OCaml version
4.02.3 (or so) along with the parser generator 'menhir'. To build and
QuickCheck the abstract domains you need the library 'qcheck' v.0.3
all of which are available through the package manager OPAM.

Furthermore we recommend 'ledit' for a nicer working environment in
the toplevel (also available in OPAM).

The QuickCheck code builds on an extended version of 'LCheck' which is
included with the prototype's source code. LCheck is a module for
randomized, property-based testing (QuickChecking) of lattices and
lattice operations.  It is furthermore described in the paper

    QuickChecking Static Analysis Properties
    Jan Midtgaard and Anders Møller, ICST'15
    http://janmidtgaard.dk/papers/Midtgaard-Moeller:ICST15.pdf  


Build instructions:
-------------------

Provided the above requirements are met, building the top-level should
be as simple as

    $ make future.top

To build the quickcheck test

    $ make domcheck


To run examples:
----------------

Once the prototype has been succesfully built simply run

    $ ./ledit ./future.top
    

Now try analyzing a simple program consisting of one processes. The
process reads a value from channel 1 and assigns the obtained value to
the variable 'y':

    # Analyzer.Intanalyzer.eval_future_top (Ast.Chread (1,"y"));;
    
                                   ([], Top*)
    1? y;                              ([y -> [-oo;+oo]], Top*) 


which says:

  * analyzing the "reading process" (started from the empty store []
    and *any* future Top*) on completion, we reach a
    post condition state consisting of
    - a store with y bound to any value [-oo;+oo]
    - any future Top* (still)

We can write the same example as a string and have it parsed up and
analyzed by Main.eval_str_pp:

    # Future.eval_str "spawn p() { ch?y }";;
    
    ch -> 0
                                   ([], Top*)
    0? y;                              ([y -> [-oo;+oo]], Top*) 

which says that the channel named 'ch' in the source program has been
numbered '0' for analysis purposes (and otherwise yields the same as
above).


Suppose we want to analyze the same program against a future which
will never output to channel 'ch'. The complement property can be
captured by the regular expression ch![-oo;+oo] . Top* (after a write
to 'ch' anything can happen). The desired property can thereby be
described as the complement of the above: ~(ch![-oo;+oo] . Top*) We
can now analyze the process against this policy, using the supplied
regular expression parser:

    # Future.eval_str_policy "spawn p() { ch?y }" "~(ch![-oo;+oo] . Top*)";;
    
                                  ([], ¬(!([0;0], [-oo;+oo]) · Top*))
    0? y;                              (Bot, Ø) 

which says that a read from channel 0 (the number for 'ch') gets us to
a bottom state -- a dead state.



To re-run the first example from the paper's introduction (the server):

    # Future.eval_proc (snd (Ast.highscore 0));;
    
    ask -> 0
    hsc -> 1
    report -> 2
    
                                  ([], Top*)
    highscore = 0;                              ([highscore -> [0;0]], Top*)
    while (true) {
      choose {
        0? cid;                              ([cid -> [-oo;+oo]; highscore -> [0;+oo]; new -> [-oo;+oo]], Top*)
        1! highscore;                              ([cid -> [-oo;+oo]; highscore -> [0;+oo]; new -> [-oo;+oo]], Top*)
      } | {
        2? new;                              ([cid -> [-oo;+oo]; highscore -> [0;+oo]; new -> [-oo;+oo]], Top*)
        if (highscore < new)
        then {
          highscore = new;                              ([cid -> [-oo;+oo]; highscore -> [1;+oo]; new -> [1;+oo]], Top*)
        } else {
          skip;                              ([cid -> [-oo;+oo]; highscore -> [0;+oo]; new -> [-oo;+oo]], Top*)
        }                              ([cid -> [-oo;+oo]; highscore -> [0;+oo]; new -> [-oo;+oo]], Top*)
      }
    }                              (Bot, Top*) 



To re-run the second example from the paper's introduction (the client):

    # Future.eval_proc_policy (snd (Ast.highscore 0)) "(ask![0;+oo] + report![0;+oo] . hsc?[-oo;+oo])*";;
    
    ask -> 0
    hsc -> 2
    report -> 1
    
                                  ([], (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*)
    highscore = 0;                              ([highscore -> [0;0]], (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*)
    while (true) {
      choose {
        0? cid;                              ([cid -> [0;+oo]; highscore -> [0;+oo]; new -> [0;+oo]], (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*)
        2! highscore;                              (Bot, Ø)
      } | {
        1? new;                              ([highscore -> [0;+oo]; new -> [0;+oo]], (?([2;2], [-oo;+oo]) · (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*))
        if (highscore < new)
        then {
          highscore = new;                              ([highscore -> [1;+oo]; new -> [1;+oo]], (?([2;2], [-oo;+oo]) · (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*))
        } else {
          skip;                              ([highscore -> [0;+oo]; new -> [0;+oo]], (?([2;2], [-oo;+oo]) · (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*))
        }                              ([highscore -> [0;+oo]; new -> [0;+oo]], (?([2;2], [-oo;+oo]) · (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*))
      }
    }                              (Bot, ((?([2;2], [-oo;+oo]) · (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*) + (!([0;0], [0;+oo]) + (!([1;1], [0;+oo]) · ?([2;2], [-oo;+oo])))*))



The file 'ast.ml' contain a number of additional examples.
These are automatically run and printed with the command './future.byte'
(after having run 'make')


To run the QuickCheck tests:
----------------------------

To re-run the QuickCheck tests in the terminal simply execute:

    $ ./redomcheck.byte 
    check 1229 properties...
    testing property leq reflexive in parity...
      [✔] passed 1000 tests (0 preconditions failed)
    testing property leq transitive in parity...
      [✔] passed 1000 tests (0 preconditions failed)
    testing property leq anti symmetric in parity...
      [✔] passed 1000 tests (0 preconditions failed)

    [...many lines cut...]

    testing property 'Prodlattice(Storelattice(interval),interval,interval).widening increasing in argument 2'...
      [✔] passed 1000 tests (0 preconditions failed)
    testing property 'Prodlattice(Storelattice(interval),interval,interval).widening invariant in argument 2'...
      [✔] passed 1000 tests (0 preconditions failed)
    tests run in 733.49s
    [✔] Success! (passed 1229 tests)
