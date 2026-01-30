/-
Copyright (c) 2024. All rights reserved.
Released under MIT license.
-/

/-- Root module for the Collatz conjecture formalization. -/
import Collatz.Basic
import Collatz.PartI
import Collatz.TiltBalance
import Collatz.IntegralityBridge
import Collatz.«1135»
import Collatz.LyapunovBakerConnection
import Hammer
#check @Collatz.collatz_conjecture_odd_universal

example : True := by
  hammer
