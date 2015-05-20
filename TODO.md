1. Document the code. Write the manual. Etc.
2. Play with the API for loading up a .au file and fiddling with the objects
   manually. We probably don't want *all* the interaction to go through the
   parser, as it's probably still buggy.
3. Once the above tools are smooth, deprecate and remove GameTools.hs and
   Games.hs.
4. Add a bunch of tests, especially for the parser. Right now, my idiot checks
   are as follows: run "main" in "Games.hs", and run "modalcombat" on
   "agents/standard.cd". More tests would be nice though.
5. Extend the modalagents tool to allow actual modal agents, e.g. agents which
   reference other agetns. Here's how I'd do it: Alter the 'Call x y' datatype
   to have "callSubagents :: [Call x y]" and then change the type of
   BuildCompetition so that it returns (Name, Env) instead of (Name,
   CompiledAgent). Then just switch out simpleMultiCompetition for
   multiCompetition; the rest is all already in place.
6. Grep around for TODOs
