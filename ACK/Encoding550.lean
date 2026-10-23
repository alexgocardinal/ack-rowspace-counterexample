import ACK.Bridge550

namespace ACK.Witness550

def booleanPrefixCode (b : Fin 14 → Bool) : Nat :=
  Nat.bit (b 0) (Nat.bit (b 1) (Nat.bit (b 2) (Nat.bit (b 3) (Nat.bit (b 4) (Nat.bit (b 5) (Nat.bit (b 6) (Nat.bit (b 7) (Nat.bit (b 8) (Nat.bit (b 9) (Nat.bit (b 10) (Nat.bit (b 11) (Nat.bit (b 12) (Nat.bit (b 13) (0))))))))))))))

theorem booleanPrefixCode_correct
    (b : Fin 14 → Bool) (k : Fin 14) :
    (booleanPrefixCode b).testBit k.val = b k := by
  fin_cases k <;>
    simp only [booleanPrefixCode,
      Nat.testBit_bit_zero, Nat.testBit_bit_succ]
  all_goals
    apply congrArg b
    apply Fin.ext
    norm_num

theorem booleanPrefixCode_lt
    (b : Fin 14 → Bool) :
    booleanPrefixCode b < 16384 := by
  change booleanPrefixCode b < 2 ^ 14
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j : Nat, i = j + 14 :=
    ⟨i - 14, by omega⟩
  simp only [booleanPrefixCode, Nat.add_succ,
    Nat.testBit_bit_succ, Nat.zero_testBit]

theorem booleanPrefixCode_split (b : Fin 14 → Bool) :
    ∃ lo hi : Fin 128,
      booleanPrefixCode b = lo.val + 128 * hi.val := by
  let m := booleanPrefixCode b
  have hm : m < 16384 := booleanPrefixCode_lt b
  have hlo : m % 128 < 128 := Nat.mod_lt m (by decide)
  have hhi : m / 128 < 128 := by omega
  refine ⟨⟨m % 128, hlo⟩, ⟨m / 128, hhi⟩, ?_⟩
  change m = m % 128 + 128 * (m / 128)
  omega

end ACK.Witness550

#print axioms ACK.Witness550.booleanPrefixCode_lt
#print axioms ACK.Witness550.booleanPrefixCode_correct
#print axioms ACK.Witness550.booleanPrefixCode_split
