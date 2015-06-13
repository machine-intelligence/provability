1. Document the code. Write the manual. Etc.
2. Play with the API for loading up a .au file and fiddling with the objects
   manually. We probably don't want *all* the interaction to go through the
   parser, as it's probably still buggy.
3. Once the above tools are smooth, deprecate and remove GameTools.hs and
   Games.hs.
4. Add a bunch of tests, especially for the parser. Right now, my idiot checks
   are as follows: run "main" in "Games.hs", and run "modalcombat" on
   "agents/standard.cd". More tests would be nice though.
5. Grep around for TODOs
