1. Fix the code. Write tests. It's compiling, but it hasn't been run yet.
   (Right now, my idiot checks are as follows: run "main" in "Games.hs", and
   run "modalcombat" on "agents/standard.cd". More tests would be nice though.)
2. Write a preprocessor that strips commens and adds 'end' markers.
3. Write a agents/test.mc file that demonstrates how things work.
4. Play with the API for loading up a .mc file and fiddling with the objects
   manually. We probably don't want *all* the interaction to go through the
   new language compiler, as it's probably still buggy (and it's not as
   powerful as manipulating the formula maps manually).
5. Remove or upgrade all the "dying files" discussed in the README.
6. Grep around for TODOs
