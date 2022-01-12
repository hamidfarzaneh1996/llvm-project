; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-pc-linux -relocation-model=pic | FileCheck %s

define void ()* @g() {
; CHECK-LABEL: g:
; CHECK:       # %bb.0: # %entry
; CHECK-NEXT:    leaq {{.*}}(%rip), %rax
; CHECK-NEXT:    retq
entry:
	ret void ()* @f
}

declare hidden void @f()
