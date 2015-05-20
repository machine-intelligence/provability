1. Document the code. Write the manual. Etc.
2. Either change Name = String or stop using printf, perhaps both. Lots of code
   is needlessly complicated by all the Text.(un)packing.
3. Play with the API for loading up a .au file and fiddling with the objects
   manually. We probably don't want *all* the interaction to go through the
   parser, as it's probably still buggy.
4. Once the above tools are smooth, deprecate and remove GameTools.hs and
   Games.hs.
5. Add a bunch of tests, especially for the parser. Right now, my idiot checks
   are as follows: run "main" in "Games.hs", and run "modalcombat" on
   "agents/standard.cd". More tests would be nice though.
6. Grep around for TODOs
