open HolKernel boolLib Parse bossLib

val _ = new_theory "option_state"

val OPTS_FAIL_def = Define`
  OPTS_FAIL = (\s. NONE)`;

val OPTS_UNIT_def = Define`
  OPTS_UNIT a = (\s. SOME (a,s))
`;

val OPTS_BIND_def = Define`
  OPTS_BIND m f = \s. OPTION_BIND (m s) (UNCURRY f)
`;

val OPTS_UNIT_BIND_def = Define`
  OPTS_UNIT_BIND m1 m2 = \s. OPTION_BIND (m1 s) (\v. m2 (SND v))
`;

val _ = overload_on("monad_bind", ``OPTS_BIND``);
val _ = overload_on("monad_unitbind", ``OPTS_UNIT_BIND``);
val _ = overload_on("return", ``OPTS_UNIT``);

val _ = export_theory ()
