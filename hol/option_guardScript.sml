open HolKernel bossLib

val _ = new_theory "option_guard"

val OPTION_GUARD_def = Define`
  OPTION_GUARD b = if b then SOME () else NONE`;

val OPTION_IGNORE_BIND_def = Define`
  OPTION_IGNORE_BIND m1 m2 = OPTION_BIND m1 (K m2)`;

val _ = export_theory ()
