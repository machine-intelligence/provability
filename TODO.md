Something is broken in Games.hs! (Compare this branch to master.)

Eventually, I'd like to be able to write and run files like the following:

    agent UDT(number start=0, number step=0)
      let $level = $start
      for $o in theirActions
        for $a in myActions
           if □⌜UDT(U)=$a → U(UDT)=$o⌝
             return $a
           let $level = $level + $step

    universe FiveAndTen outcomes=[10, 5]
      if A()=5
        return 5
      return 10

    play FiveAndTen UDT[5, 10]

    ------------------------------------------

    universe Newcomb(number level=0) outcomes=[1001000, 1000000, 1000, 0]
      if A()=2 and [$level]⌜A()=1⌝
         return 1001000
      if A()=1 and [$level]⌜A()=1⌝
         return 1000000
      if A()=2
         return 1000
      return 0

    play Newcomb(10) UDT(0, 1)[1, 2]

    ------------------------------------------

    universemap Agame($level) [Good, Bad]
      Good ↔ [$level]⌜A()=A⌝
      Bad ↔ ¬[$level]⌜A()=A⌝
    universemap Bgame($level) [Good, Bad]
      Good ↔ [$level]⌜A()=B⌝
      Bad ↔ ¬[$level]⌜A()=B⌝

    play Agame UDT(step=1)[A, B]
    play Bgame UDT(step=1)[A, B]

    ------------------------------------------

    universeN 2 PD
      if A1()=D and A2()=C
        return DC
      if A1()=C and A2()=C
        return CC
      if A1()=D and A2()=D
        return DD
      return CD

    -- OR --

    universeNmap 2 PD
      DC ↔ A1()=D and A2()=C
      CC ↔ A1()=C and A2()=C
      DD ↔ A1()=D and A2()=D
      CD ↔ A1()=C and A2()=D

    playN 2
      PD
      UDT(step=1)[C, D][DC, CC, DD, CD]
      UDT(step=1)[C, D][CD, CC, DD, DC]

It's going to take a little while to get there from here, but here's my
roadmap:

1. Generalize the relVar parser so that it can handle more than just "Me" and
   "Them". Figure out how to pass those parameters around. Expose those
   parameters all the way up through the agentParsers.
2. Generalize Statement, CodeFragment, Code, and Agent in some way that allows
   them to use other variable types besides just ModalVars. This is necessary
   if we want to be able to define Universes which refer to many agents (rather
   than assuming that everybody refers to exactly one opponent.)
3. Overhaul the code in Universes.hs such that it can parse the above syntax.
4. Remove GameTools.hs, which will be obsoleted by step 3.
5. Starting from ModalCombat.hs, write a tool that reads and executes files
   written in the above format.
