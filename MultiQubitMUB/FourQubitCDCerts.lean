import MultiQubitMUB.FourQubitCDCerts1
import MultiQubitMUB.FourQubitCDCerts2
import MultiQubitMUB.FourQubitCDCerts3
import MultiQubitMUB.FourQubitCDCerts4
import MultiQubitMUB.FourQubitCDCerts5
import MultiQubitMUB.FourQubitCDCerts6

namespace MultiQubitMUB
namespace FourQubitCD

def sp42Certs (i : Fin 42) : Cert56 :=
  match i.val with
  | 0 => sp42Cert_0
  | 1 => sp42Cert_1
  | 2 => sp42Cert_2
  | 3 => sp42Cert_3
  | 4 => sp42Cert_4
  | 5 => sp42Cert_5
  | 6 => sp42Cert_6
  | 7 => sp42Cert_7
  | 8 => sp42Cert_8
  | 9 => sp42Cert_9
  | 10 => sp42Cert_10
  | 11 => sp42Cert_11
  | 12 => sp42Cert_12
  | 13 => sp42Cert_13
  | 14 => sp42Cert_14
  | 15 => sp42Cert_15
  | 16 => sp42Cert_16
  | 17 => sp42Cert_17
  | 18 => sp42Cert_18
  | 19 => sp42Cert_19
  | 20 => sp42Cert_20
  | 21 => sp42Cert_21
  | 22 => sp42Cert_22
  | 23 => sp42Cert_23
  | 24 => sp42Cert_24
  | 25 => sp42Cert_25
  | 26 => sp42Cert_26
  | 27 => sp42Cert_27
  | 28 => sp42Cert_28
  | 29 => sp42Cert_29
  | 30 => sp42Cert_30
  | 31 => sp42Cert_31
  | 32 => sp42Cert_32
  | 33 => sp42Cert_33
  | 34 => sp42Cert_34
  | 35 => sp42Cert_35
  | 36 => sp42Cert_36
  | 37 => sp42Cert_37
  | 38 => sp42Cert_38
  | 39 => sp42Cert_39
  | 40 => sp42Cert_40
  | _ => sp42Cert_41

def sp42S64List : List (List ℤ) := [
  sp42Cert_0.s64,
  sp42Cert_1.s64,
  sp42Cert_2.s64,
  sp42Cert_3.s64,
  sp42Cert_4.s64,
  sp42Cert_5.s64,
  sp42Cert_6.s64,
  sp42Cert_7.s64,
  sp42Cert_8.s64,
  sp42Cert_9.s64,
  sp42Cert_10.s64,
  sp42Cert_11.s64,
  sp42Cert_12.s64,
  sp42Cert_13.s64,
  sp42Cert_14.s64,
  sp42Cert_15.s64,
  sp42Cert_16.s64,
  sp42Cert_17.s64,
  sp42Cert_18.s64,
  sp42Cert_19.s64,
  sp42Cert_20.s64,
  sp42Cert_21.s64,
  sp42Cert_22.s64,
  sp42Cert_23.s64,
  sp42Cert_24.s64,
  sp42Cert_25.s64,
  sp42Cert_26.s64,
  sp42Cert_27.s64,
  sp42Cert_28.s64,
  sp42Cert_29.s64,
  sp42Cert_30.s64,
  sp42Cert_31.s64,
  sp42Cert_32.s64,
  sp42Cert_33.s64,
  sp42Cert_34.s64,
  sp42Cert_35.s64,
  sp42Cert_36.s64,
  sp42Cert_37.s64,
  sp42Cert_38.s64,
  sp42Cert_39.s64,
  sp42Cert_40.s64,
  sp42Cert_41.s64
]

theorem sp42Certs_valid (i : Fin 42) : checkCert56 (sp42Certs i) = true := by
  rcases i with ⟨v, hv⟩
  interval_cases v
  · exact sp42Cert_0_valid
  · exact sp42Cert_1_valid
  · exact sp42Cert_2_valid
  · exact sp42Cert_3_valid
  · exact sp42Cert_4_valid
  · exact sp42Cert_5_valid
  · exact sp42Cert_6_valid
  · exact sp42Cert_7_valid
  · exact sp42Cert_8_valid
  · exact sp42Cert_9_valid
  · exact sp42Cert_10_valid
  · exact sp42Cert_11_valid
  · exact sp42Cert_12_valid
  · exact sp42Cert_13_valid
  · exact sp42Cert_14_valid
  · exact sp42Cert_15_valid
  · exact sp42Cert_16_valid
  · exact sp42Cert_17_valid
  · exact sp42Cert_18_valid
  · exact sp42Cert_19_valid
  · exact sp42Cert_20_valid
  · exact sp42Cert_21_valid
  · exact sp42Cert_22_valid
  · exact sp42Cert_23_valid
  · exact sp42Cert_24_valid
  · exact sp42Cert_25_valid
  · exact sp42Cert_26_valid
  · exact sp42Cert_27_valid
  · exact sp42Cert_28_valid
  · exact sp42Cert_29_valid
  · exact sp42Cert_30_valid
  · exact sp42Cert_31_valid
  · exact sp42Cert_32_valid
  · exact sp42Cert_33_valid
  · exact sp42Cert_34_valid
  · exact sp42Cert_35_valid
  · exact sp42Cert_36_valid
  · exact sp42Cert_37_valid
  · exact sp42Cert_38_valid
  · exact sp42Cert_39_valid
  · exact sp42Cert_40_valid
  · exact sp42Cert_41_valid

end FourQubitCD
end MultiQubitMUB
