Eventually, I'd like to be able to write and run files like the following:

    agent UDT(action default, number start=0, number step=0)
      let $level = $start
      for outcome $o in [...]
        for action $a in [...]
           if □⌜UDT(U)=$a → U(UDT)=$o⌝
             return $a
           let $level = $level + $step
      return $default
    end

    universe FiveAndTen actions=[5, 10] outcomes=[10, 5]
      if A()=@5
        return $5
      return $10
    end

    play FiveAndTen UDT(@5)

    ------------------------------------------

    universe Newcomb(number level=0) actions=[1, 2] outcomes=[1001000, 1000000, 1000, 0]
      if A()=@2 and [$level]⌜A()=@1⌝
         return $1001000
      if A()=@1 and [$level]⌜A()=@1⌝
         return $1000000
      if A()=@2
         return $1000
      return 0
    end

    play Newcomb(#10) UDT(@2, step=#1)

    ------------------------------------------

    umap Agame($level) actions=[A, B] outcomes=[Good, Bad]
      $Good ↔ [$level]⌜A()=@A⌝
      $Bad ↔ ¬[$level]⌜A()=@A⌝
    end

    umap Bgame($level) actions=[A, B] outcomes=[Good, Bad]
      $Good ↔ [$level]⌜A()=@B⌝
      $Bad ↔ ¬[$level]⌜A()=@B⌝
    end

    play Agame UDT(@A, #0, #1)
    play Bgame UDT(@A, #0, #1)

    ------------------------------------------

    universe PD
      if A1()=@D and A2()=@C
        return $DC
      if A1()=@C and A2()=@C
        return $CC
      if A1()=@D and A2()=@D
        return $DD
      return $CD
    end

    -- OR --

    umap PD
      DC ↔ A1()=D and A2()=C
      CC ↔ A1()=C and A2()=C
      DD ↔ A1()=D and A2()=D
      CD ↔ A1()=C and A2()=D
    end

    play PD
      UDT(@D, step=#1)[C, D][DC, CC, DD, CD]
      UDT(@D, step=#1)[C, D][CD, CC, DD, DC]

Here's my roadmap to get there from here:

1. Write a parser for the above. I began one in Universe.hs, but it's still
   pretty limited.
2. Write a command line tool that reads and executes these files.
   ModalCombat.hs is an example of how to do this.

Other things on the todo list:

3. Once the above tools exist, revisit Games.hs and GameTools.hs. They will be
   duplicating functionality, and likely should be obsoleted -- although
   perhaps we'll want to improve the tools for building & running games in
   Haskell (rather than just via the parser) before we do so.
4. Document everything better.
5. Add tests. Right now, my idiot checks are as follows: run "main" in
   "Games.hs", and run "modalcombat" on "agents/standard.cd". More tests would
   be nice though.
