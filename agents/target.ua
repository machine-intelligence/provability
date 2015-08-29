--------------------------------------------------------------------------
-- This is our standard modal version of UDT.
-- (Parameterized by default action, staring proof level, and proof escalation
-- amount.)

theory UDT(action default, number level=0, number step=0)
	let &n = &level
	for outcome &o in outcomes
		for action &a in actions
			if [&n]⌜A()=&a → U()=&o⌝
				return &a
			let &n = &n + &step
	return &default

--------------------------------------------------------------------------
-- Here are some simple decision problems.

problem FiveAndTen [$10, $5] [10, 5]
	if A()=5
		return $5
	return $10

problem Newcomb(number level=0) [$1001000, $1000000, $1000, $0] [1, 2]
	if A()=2 and [&level]⌜A()=1⌝
		return $1001000
	if A()=1 and [&level]⌜A()=1⌝
		return $1000000
	if A()=2
		return $1000
	return $0

problem map 5and10 [$10, $5] [5, 10]
	$5 ↔ A()=5
	$10 ↔ A()=10

problem map PD [$DC, $CC, $DD, $CD] [C, D]
	$DC ↔ A1()=D and A2()=C
	$CC ↔ A1()=C and A2()=C
	$DD ↔ A1()=D and A2()=D
	$CD ↔ A1()=C and A2()=D

bot CooperateBot = ⊤

bot DefectBot = ⊥

agent FairBot
	if □⌜Them(Me)=C⌝
		return C
	return D

agent PrudentBot
	if [1]⌜Them(DefectBot)=D⌝ and □⌜Them(Me)=C⌝
		return C
	return D

combat with frames! PrudentBot vs FairBot

compete: PrudentBot vs FairBot

play with map with frames: FiveAndTen, UDT(5).
play: Newcomb, UDT(2, step=1).
play: Newcomb(1), UDT(2, level=10, step=1).
play: 5and10, UDT(5).
play: 5and10, UDT(10).
play: PD,
	UDT(D, step=1)[...][$DC, $CC, $DD, $CD],
	UDT(D, step=1)[...][$CD, $CC, $DD, $DC].
