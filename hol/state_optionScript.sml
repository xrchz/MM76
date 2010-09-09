open HolKernel boolLib Parse bossLib

val _ = new_theory "state_option"

val _ = type_abbrev("state_option", ``:'a -> ('b # 'a) option``);
val _ = temp_type_abbrev("monad", ``:('a,'b) state_option``);

val STATE_OPTION_FAIL_def = Define`
  STATE_OPTION_FAIL : ('a,'b) monad
  s = NONE`;

val STATE_OPTION_UNIT_def = Define`
  STATE_OPTION_UNIT : 'b -> ('a,'b) monad
  a s = SOME (a,s)`;

val STATE_OPTION_BIND_def = Define`
  STATE_OPTION_BIND : ('a,'b) monad -> ('b -> ('a,'c) monad) -> ('a,'c) monad
  m f s = OPTION_BIND (m s) (UNCURRY f)`;

val STATE_OPTION_IGNORE_BIND_def = Define`
  STATE_OPTION_IGNORE_BIND : ('a,'b) monad -> ('a,'c) monad -> ('a,'c) monad
  m1 m2 s = OPTION_BIND (m1 s) (m2 o SND)`;

val STATE_OPTION_LIFT_def = Define`
  STATE_OPTION_LIFT : 'b option -> ('a,'b) monad
  m s = OPTION_BIND m (λa. SOME (a,s))`;

val _ = overload_on("monad_bind", ``STATE_OPTION_BIND o STATE_OPTION_LIFT``);
val _ = overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND o STATE_OPTION_LIFT``);
val _ = overload_on("monad_bind", ``STATE_OPTION_BIND``);
val _ = overload_on("monad_unitbind", ``STATE_OPTION_IGNORE_BIND``);
val _ = overload_on("return", ``STATE_OPTION_UNIT``);

val _ = export_theory ()
