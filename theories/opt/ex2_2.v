From stbor.sim Require Import local invariant one_step.

Set Default Proof Using "Type".

Definition ex2_2 : function :=
  fun: ["x"],
    Retag "x"  FnEntry ;;
    let: "v" := Copy *{int} "x" in
    Call #[ScFnPtr "f"] ["x"] ;;
    "v"
    .

Definition ex2_2_opt : function :=
  fun: ["x"],
    Retag "x"  FnEntry ;;
    Call #[ScFnPtr "f"] ["x"] ;;
    Copy *{int} "x"
    .
