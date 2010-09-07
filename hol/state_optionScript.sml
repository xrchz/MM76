open HolKernel boolLib Parse bossLib

val _ = new_theory "state_option"

val STATE_OPTION_FAIL_def = Define`
  STATE_OPTION_FAIL s = NONE`;

val STATE_OPTION_UNIT_def = Define`
  STATE_OPTION_UNIT a s = SOME (a,s)`;

val STATE_OPTION_BIND_def = Define`
  STATE_OPTION_BIND m f s = OPTION_BIND (m s) (UNCURRY f)`;

val STATE_OPTION_IGNORE_BIND_def = Define`
  STATE_OPTION_IGNORE_BIND m1 m2 s = OPTION_BIND (m1 s) (m2 o SND)`;

val STATE_OPTION_LIFT_def = Define`
  STATE_OPTION_LIFT m s = OPTION_BIND m (λa. SOME (a,s))`;

val _ = overload_on("monad_bind", ``STATE_OPTION_BIND``);
val _ = overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND``);
val _ = overload_on("return", ``STATE_OPTION_UNIT``);

val _ = export_theory ()
