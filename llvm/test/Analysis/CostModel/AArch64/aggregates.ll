; NOTE: Assertions have been autogenerated by utils/update_analyze_test_checks.py
; RUN: opt < %s -mtriple=aarch64-unknown-linux-gnu -cost-model -cost-kind=throughput -analyze | FileCheck %s --check-prefixes=ALL,THROUGHPUT
; RUN: opt < %s -mtriple=aarch64-unknown-linux-gnu -cost-model -cost-kind=latency -analyze | FileCheck %s --check-prefixes=ALL,LATENCY
; RUN: opt < %s -mtriple=aarch64-unknown-linux-gnu -cost-model -cost-kind=code-size -analyze | FileCheck %s --check-prefixes=ALL,CODESIZE

define i32 @extract_first_i32({i32, i32} %agg) {
; ALL-LABEL: 'extract_first_i32'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, i32 } %agg, 0
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret i32 %r
;
  %r = extractvalue {i32, i32} %agg, 0
  ret i32 %r
}

define i32 @extract_second_i32({i32, i32} %agg) {
; ALL-LABEL: 'extract_second_i32'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, i32 } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret i32 %r
;
  %r = extractvalue {i32, i32} %agg, 1
  ret i32 %r
}

define i32 @extract_i32({i32, i1} %agg) {
; ALL-LABEL: 'extract_i32'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, i1 } %agg, 0
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret i32 %r
;
  %r = extractvalue {i32, i1} %agg, 0
  ret i32 %r
}

define i1 @extract_i1({i32, i1} %agg) {
; ALL-LABEL: 'extract_i1'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, i1 } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret i1 %r
;
  %r = extractvalue {i32, i1} %agg, 1
  ret i1 %r
}

define float @extract_float({i32, float} %agg) {
; ALL-LABEL: 'extract_float'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, float } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret float %r
;
  %r = extractvalue {i32, float} %agg, 1
  ret float %r
}

define [42 x i42] @extract_array({i32, [42 x i42]} %agg) {
; ALL-LABEL: 'extract_array'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, [42 x i42] } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret [42 x i42] %r
;
  %r = extractvalue {i32, [42 x i42]} %agg, 1
  ret [42 x i42] %r
}

define <42 x i42> @extract_vector({i32, <42 x i42>} %agg) {
; ALL-LABEL: 'extract_vector'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, <42 x i42> } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret <42 x i42> %r
;
  %r = extractvalue {i32, <42 x i42>} %agg, 1
  ret <42 x i42> %r
}

%T1 = type { i32, float, <4 x i1> }

define %T1 @extract_struct({i32, %T1} %agg) {
; ALL-LABEL: 'extract_struct'
; ALL-NEXT:  Cost Model: Found an estimated cost of 0 for instruction: %r = extractvalue { i32, %T1 } %agg, 1
; ALL-NEXT:  Cost Model: Found an estimated cost of 1 for instruction: ret %T1 %r
;
  %r = extractvalue {i32, %T1} %agg, 1
  ret %T1 %r
}