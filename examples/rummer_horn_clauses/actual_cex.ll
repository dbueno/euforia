; ModuleID = 'harness'
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"

@0 = private constant [1 x i32] [i32 1]
@1 = private global i32 0

define i32 @__VERIFIER_nondet_int() {
entry:
  %0 = load i32, i32* @1
  %1 = add i32 %0, 1
  store i32 %1, i32* @1
  %2 = call i32 @__seahorn_get_value_i32(i32 %0, i32* getelementptr inbounds ([1 x i32], [1 x i32]* @0, i32 0, i32 0), i32 1)
  ret i32 %2
}

declare i32 @__seahorn_get_value_i32(i32, i32*, i32)
