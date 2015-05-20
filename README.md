Lightning overview:

`Modal/Formulas.hs` is the starting point. That's where the modal formula data
structure is defined, and that's where the fixed point solver lives.

The other files are as follows:

`ModalCombat.hs`: The file implementing the `modalcombat` executable, which
runs on files such as the one found in `agents/standard.cd`. (See that file for
an example of what sort of syntax is supported.)

`Modal/Combat.hs`: Implements the parser used by `ModalCombat.hs` to parse
files such as `agents/standard.cd`. This is basically the
shared-source-code-prisoner's-dilemma-specific parser code (built on top of the
generic-modal-agent parser code of `Modal/Code.hs`).

`ModalAgents.hs`: is `ModalCombat.hs` but for the `modalagents` executable.

`Modal/Universes.hs`: is `Combat.hs` but for the Modal UDT framework.

`Modal/Code.hs`: The meat of the parser, and contains all the machinery that
turns modal programs into modal formulas.

`Modal/Environment.hs`: Defines environments full of modal agents. This is the
structure that allows us to track which modal agents refer to other modal
agents, and ensure that modal agents are well-founded (e.g. that they don't go
into cycles where X calls Y on Z, and Z calls Y on X).

`Modal/Competition.hs`: This basically takes a bunch of agents and builds a map
of formulas for use by the fixpoint evaluator. It can currently either (a) take
one environment and two names, and play those agents against each other in the
same environment; (b) take two environments and two names, and play two
different types of agents against each other; (c) take a host of agents and
play them all in a multi-agent game. That third category doesn't use the
environment machinery, yet, and so agents in multi-agent games can't talk about
what would happen if they played their opponent against some other opponent.
This is in part because I'm not entirely sure how that should work, but mostly
because I didn't implement it yet.

`Modal/Programming.hs`: This file provides some tools for making modal agents
in Haskell (rather than in the still-rough-around-the-edges modal program
language). Eventually the modal programming language may supersede the tools in
this file, but we'll probably keep them around anyway, as it's occasionally
quite useful to hack together a modal agent in ghci.

`Modal/GameTools.hs`: A file that makes it easier to evaluate agents in
multi-player games. This file is slowly being deprecated by upgrades to
`Code.hs`, but it will be a little while before we get 3+ player games working
with the modal agent code.

`Modal/Agents.hs`: Various haskell implementations of UDT (using the tools in
`Modal/Programming.hs` rather than the modal agent programming language).

`Modal/Games.hs`: Various haskell implementations of modal games
(hand-specified), including the 5 and 10 problem, the Newcomb problem, and so
on. (This may eventually be deprecated by the upgrades discussed in `TODO.md`.)

`Modal/Utilities.hs`: contains some haskell convenience tools (such as
functions which turn Either x a into IO a, etc).

`Modal/Parser.hs`: contains some parsec convenience tools (such as a Parsable
typeclass, etc).

`Modal/Display.hs`: contains some display convenience tools (such as code for
rendering maps, etc).
