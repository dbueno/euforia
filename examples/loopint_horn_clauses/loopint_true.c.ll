; ModuleID = '/benchmarks/loopint_true.c.bc'
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-unknown-linux-gnu"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

declare i32 @__VERIFIER_nondet_int() #0

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter()

; Function Attrs: nounwind
define i32 @main() #2 {
entry:
  tail call void @seahorn.fn.enter() #3
  %0 = tail call i32 @__VERIFIER_nondet_int() #3
  %1 = icmp eq i32 %0, 0
  tail call void @verifier.assume(i1 %1) #3
  br label %2

; <label>:2                                       ; preds = %4, %entry
  %i.0.i = phi i32 [ %0, %entry ], [ %5, %4 ]
  %3 = icmp slt i32 %i.0.i, 7
  br i1 %3, label %4, label %verifier.error.loopexit

; <label>:4                                       ; preds = %2
  %5 = add nsw i32 %i.0.i, 3
  %6 = icmp slt i32 %5, 5
  br i1 %6, label %2, label %7

; <label>:7                                       ; preds = %4
  %.lcssa = phi i32 [ %5, %4 ]
  %8 = icmp slt i32 %.lcssa, 7
  tail call void @verifier.assume.not(i1 %8) #3
  br label %verifier.error

verifier.error.loopexit:                          ; preds = %2
  br label %verifier.error

verifier.error:                                   ; preds = %verifier.error.loopexit, %7
  tail call void @seahorn.fail() #3
  ret i32 42
}

attributes #0 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0 (tags/RELEASE_380/final)"}
