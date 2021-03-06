//===------ LoopInversion.h ----------------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// Try to reduce the number of scatter dimension. Useful to make isl_union_map
// schedules more understandable. This is only intended for debugging and
// unittests, not for optimizations themselves.
//
//===----------------------------------------------------------------------===//

#ifndef POLLY_LOOP_INVERSION_H
#define POLLY_LOOP_INVERSION_H

namespace llvm {
class PassRegistry;
class Pass;
} // namespace llvm

namespace polly {
llvm::Pass *createLoopInversionPass();
} // namespace polly

namespace llvm {
void initializeLoopInversionPass(llvm::PassRegistry &);
} // namespace llvm

#endif /* POLLY_LOOP_INVERSION_H */
