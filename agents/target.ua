%------------------------------------------------------------------------
% □ Line comments
% □ Block comments
% ✓ Extend Bivar
% ✓ Extend Multivar
% ✓ Outer variables don't need # signs
% ✓ Inner variables use & signs
% ✓ Statement variables must be prefixed with @ or $
% ✓ Argument types become single-character
% ✓ For loops use special characters
% ✓ Fix defParser
% ✓ Refactor map parser
% □ Allow outcome extraction from map
% □ Agent
% □ universe
% □ Bot
% ✓ Fix MultiVar competition display
% □ Add environment parsing
% □ Add with parser
% □ Add combat
% □ Add compete
% □ Add challenge
% □ test: UDT-ish agent that delegates.
% □ test: Universe that delegates.
% □ test: UDT-ish agent that iterates numbers.

% 4. Vim syntax files
% This is UDT.
% You can make it escalate or whatever.

agent UDT(@default, #start=0, #step=0):
  let level = start
  for o in $[...]
    for a in @[...]
       if □⌜Me()=&a → Them()=&o⌝
         return a
       end
       let level = level + step
     end
  end
  return default
end

--------------------------------------------------------------------------
-- Some simple problems.

universe FiveAndTen @[5, 10] $[10, 5]:
  if A()=@5
    return $5
  end
  return $10
end

universe EasyNewcomb $[1001000, 1000000, 1000, 0]:
  if A()=@2 and A()=@1
     return $1001000
  end
  if A()=@1 and A()=@1
     return $1000000
  end
  if A()=@2
     return $1000
  end
  return $0
end

universe Newcomb(number level=0) $[1001000, 1000000, 1000, 0]:
  if A()=@2 and [#level]⌜A()=@1⌝
     return $1001000
  end
  if A()=@1 and [#level]⌜A()=@1⌝
     return $1000000
  end
  if A()=@2
     return $1000
  end
  return $0
end

universe map 5and10:
  $5 ↔ A()=@5,
  $10 ↔ A()=@10,
end

universe map PD:
  $DC ↔ A1()=@D and A2()=@C,
  $CC ↔ A1()=@C and A2()=@C,
  $DD ↔ A1()=@D and A2()=@D,
  $CD ↔ A1()=@C and A2()=@D,
end


bot CooperateBot = ⊤

bot DefectBot = ⊥

agent FairBot @[C, D] $[C, D]:
  if □⌜Them(Me)=$C⌝
    return @C
  end
  return @D
end

competition env PDbase:
  CooperateBot as CB,
  DefectBot as DB,
  FairBot as FB,
end

agent PrudentBot @[C, D] $[C, D]:
  if [1]⌜Them(DB)=$D⌝ and □⌜Them(Me)=$C⌝
    return @C
  end
  return $D
end

competition env PDbots extends PDbase:
  PrudentBot as PB
end

combat in PDbots with frames: PB, FB.
compete with map with frames: CooperateBot, FB from Standard.

play with map with frames:
  FiveAndTen as U,
  UDT(@5) as A
end

play:
  EasyNewcomb as U,
  UDT(@2, step=1) as A
end

play:
  Newcomb(0) as U,
  UDT(@2, level=10, step=1) as A
end

play:
  5and10 as U,
  UDT(@5) as A
end

play:
  PD,
  UDT(@D, step=1)[@C, @D][$DC, $CC, $DD, $CD] as A1,
  UDT(@D, step=1)[@C, @D][$CD, $CC, $DD, $DC] as A2
end


% agent {name} [args] [acts] [outs] {code}
% agent map {name} [args] [outs] {map}
% universe {name} [args] [acts] [outs] {code}
% universe map {name} [args] [outs] {map}
% bot {name} = {forumla}
% combat in {env} [with maps | frames] {name} {name}
% compete [with maps | frames] {call a} {call a}
% challenge [with maps | frames] {call u} {call a...}
% environment {call}
