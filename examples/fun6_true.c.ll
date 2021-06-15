; ModuleID = 'fun5_false.c.bc'
source_filename = "fun5_false.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@a = internal unnamed_addr global i32 0, align 4
@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp uwtable
define internal fastcc void @f() unnamed_addr #0 {
  call void @seahorn.fn.enter() #2
  %1 = load i32, i32* @a, align 4, !tbaa !4
  %2 = add nsw i32 %1, 1
  store i32 %2, i32* @a, align 4, !tbaa !4
  call fastcc void @g()
  ret void
}

; Function Attrs: nounwind ssp uwtable
define internal fastcc void @g() unnamed_addr #0 {
  call void @seahorn.fn.enter() #2
  %1 = load i32, i32* @a, align 4, !tbaa !4
  %2 = add nsw i32 %1, 1
  store i32 %2, i32* @a, align 4, !tbaa !4
  ret void
}

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #0 {
  store i32 0, i32* @a, align 4
  call void @seahorn.fn.enter() #2
  call fastcc void @f()
  call fastcc void @f()
  %1 = load i32, i32* @a, align 4, !tbaa !4
  %2 = icmp eq i32 %1, 4
  br i1 %2, label %4, label %3

; <label>:3:                                      ; preds = %0
  call void @seahorn.fail() #2
  unreachable

; <label>:4:                                      ; preds = %0
  ret i32 0
}

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 5.0.0 (tags/RELEASE_500/final)"}
!4 = !{!5, !5, i64 0}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
