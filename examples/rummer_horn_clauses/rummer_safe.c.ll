; ModuleID = '/benchmarks/rummer_safe.c.bc'
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
  %1 = icmp sgt i32 %0, -1
  tail call void @verifier.assume(i1 %1) #3
  tail call void @seahorn.fn.enter() #3
  %2 = icmp sgt i32 %0, 0
  br i1 %2, label %tailrecurse.i.preheader, label %f.exit

tailrecurse.i.preheader:                          ; preds = %entry
  br label %tailrecurse.i

tailrecurse.i:                                    ; preds = %tailrecurse.i.preheader, %tailrecurse.i
  %n.tr2.i = phi i32 [ %3, %tailrecurse.i ], [ %0, %tailrecurse.i.preheader ]
  %3 = add nsw i32 %n.tr2.i, -1
  tail call void @seahorn.fn.enter() #3
  %4 = icmp sgt i32 %n.tr2.i, 1
  br i1 %4, label %tailrecurse.i, label %f.exit.loopexit

f.exit.loopexit:                                  ; preds = %tailrecurse.i
  br label %f.exit

f.exit:                                           ; preds = %f.exit.loopexit, %entry
  %accumulator.tr.lcssa.i = phi i1 [ true, %entry ], [ false, %f.exit.loopexit ]
  tail call void @verifier.assume.not(i1 %accumulator.tr.lcssa.i) #3
  tail call void @seahorn.fail() #3
  ret i32 42
}

attributes #0 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.0 (tags/RELEASE_380/final)"}
