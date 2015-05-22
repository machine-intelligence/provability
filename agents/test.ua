theory UDT(@default, #start=0, #step=0) where
  let level = start
  for outcome o in [...]
    for action a in [...]
       if □⌜Me()=&a → Them()=&o⌝ then
         return a
       end
       let level = level + step
     end
  end
  return default
end

problem FiveAndTen @[5, 10] $[10, 5]
  if A()=@5
    return $5
  end
  return $10
end

problem EasyNewcomb @[1, 2] $[1001000, 1000000, 1000, 0]
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

problem Newcomb(number level=0) @[1, 2] $[1001000, 1000000, 1000, 0]
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

umap alt5and10 actions=[@5, @10] outcomes=[$10, $5] where
  $5 ↔ ⊤;
  $10 ↔ ⊥;
end

umap PD actions=[@C, @D] outcomes=[$DC, $CC, $DD, $CD] where
  $DC ↔ A1()=@D and A2()=@C;
  $CC ↔ A1()=@C and A2()=@C;
  $DD ↔ A1()=@D and A2()=@D;
  $CD ↔ A1()=@C and A2()=@D;
end

describe(FiveAndTen as U, UDT(@5) as A)
play(EasyNewcomb as U, UDT(@2, step=1) as A)
play(Newcomb(0) as U, UDT(@2, level=10, step=1) as A)
play(alt5and10, UDT(@5) as A)

play(PD,
  UDT(@D, step=1)[@C, @D][$DC, $CC, $DD, $CD] as A1,
  UDT(@D, step=1)[@C, @D][$CD, $CC, $DD, $DC] as A2)
