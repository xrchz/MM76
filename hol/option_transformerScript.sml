open HolKernel bossLib Parse state_transformerTheory monadsyntax

val _ = new_theory "option_transformer"

val OPTIONT_FAIL_def = Define`
  OPTIONT_FAIL = UNIT NONE`;

val OPTIONT_UNIT_def = Define`
  OPTIONT_UNIT a = UNIT (SOME a)`;

val OPTIONT_LIFT_def = Define`
  OPTIONT_LIFT m = BIND m OPTIONT_UNIT`;

val OPTIONT_BIND_def = Define`
  OPTIONT_BIND m f = BIND m (λa. case a of NONE -> UNIT NONE || SOME a' -> f a')`;

val _ = overload_on("monad_bind", ``OPTIONT_BIND``);
val _ = overload_on("monad_bind", ``BIND``);
val _ = overload_on("return", ``OPTIONT_UNIT``);
val _ = overload_on("return", ``UNIT``);

val _ = export_theory ()
