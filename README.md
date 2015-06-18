Lightning overview:

`Modal/Formulas.hs` is the starting point. That's where the modal formula data
structure is defined, and that's where the fixed point solver lives.

The other files are as follows: (Read in order to understand the code)

`Modal/CompilerBase.hs`: Contains basic types used throughout the compiler,
such as Ref, Relation, and all the error types.

`Modal/Statement.hs`: Contains the definition and parser for "statements",
which are like modal formulas but can refer to variables at the meta level.
They can be turned into a formula given a context. (For example, "A()=&a
→ U()=&u" can be turned into a formula given a context containing both a and
u.)

`Modal/Code.hs`: Contains the definition and parser for "code", including if
blocks, for blocks, etc. Can compile them down to a map of modal formulas: give
it an action it gives you a formula saying true iff the code returns that
action.

`Modal/Def.hs`: Contains the definition and parser for "defs", which are the
full agents including a name, parameters, code, etc. This file also contains
the logic for applying the parameters from a call to create the code context,
and then compiling the def into a map of modal formulas.

`Modal/Competition.hs`: This basically takes a bunch of agent maps and combines
them into the competition map evaluated by the fixpoint evaluator. It can
currently either play two modalized agents againts each other, or it can play
many modalized agents against a single unmodalized universe.

`Modal/Combat.hs`: Contains the definition of and logic for handilng files such
as `agents/test.mc` (which *totally exists* (TODO)), which consist of a series
of agent definitions and execution commands used to play agents againt seach
other or inspect their behavior.

`ModalCombat.hs`: The file implementing the `modalcombat` executable, which
runs on files such as the one found in `agents/test.mc`. (See that file for
an example of what sort of syntax is supported.)

Dying files
-----------

`Modal/Programming.hs`: This file provides some tools for making modal agents
in Haskell (rather than in the still-rough-around-the-edges modal program
language). Eventually the modal programming language may supersede the tools in
this file, but we don't necessarily want to delete it altogether. (We might
decide to add better tools for manipulating modal agents in ghci or something.)

`Modal/GameTools.hs`: A file that makes it easier to evaluate agents in
multi-player games. This file is slowly being deprecated by upgrades to
`Combat.hs`, but it will be a little while before we're comfortable enough with
multi-agent games in the language parser to justify removing this code.

`Modal/Agents.hs`: A dead file that has a bunch of agents defined in it using
an old format. They need to be evacuated to a file of their own, and then this
file can be removed.

`Modal/Games.hs`: Various haskell implementations of modal games
(hand-specified), including the 5 and 10 problem, the Newcomb problem, and so
on. This file is dying; the games need to be evacuated to a file of their own
and then this file can be removed.

Helpers
-------

`Modal/Utilities.hs`: contains some haskell convenience tools (such as
functions which turn Either x a into IO a, etc).

`Modal/Parser.hs`: contains some parsec convenience tools (such as a Parsable
typeclass, etc).

`Modal/Display.hs`: contains some display convenience tools (such as code for
rendering maps, etc).
