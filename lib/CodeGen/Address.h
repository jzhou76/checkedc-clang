//===-- Address.h - An aligned address -------------------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This class provides a simple wrapper for a pair of a pointer and an
// alignment.
//
//===----------------------------------------------------------------------===//

#ifndef LLVM_CLANG_LIB_CODEGEN_ADDRESS_H
#define LLVM_CLANG_LIB_CODEGEN_ADDRESS_H

#include "llvm/IR/Constants.h"
#include "clang/AST/CharUnits.h"

namespace clang {
namespace CodeGen {

/// An aligned address.
class Address {
  llvm::Value *Pointer;
  CharUnits Alignment;

private:
  // Chekced C
  bool _isMMPtr = false;
  bool _isMMArrayPtr = false;
  llvm::Type *originalPointerTy;
  llvm::Type *rawPointerTy;  // The inner pointer type of a _MM_ptr.

public:
  Address(llvm::Value *pointer, CharUnits alignment)
      : Pointer(pointer), Alignment(alignment) {
    assert((!alignment.isZero() || pointer == nullptr) &&
           "creating valid address with invalid alignment");
    if (pointer) {
      // Backup the original _MM_ptr type.
      originalPointerTy = pointer->getType();

      // Checked C: For _MM_ptr and _MM_array_ptr, set the pointer type
      // to be the inner raw pointer type. Without this mutation,
      // pointer dereference would fail because the compiler would try to
      // dereference an llvm::StructType.
      if (pointer->getType()->isMMPointerTy()) {
        _isMMPtr = true;
        rawPointerTy = pointer->getType()->getMMPtrInnerPtrTy();
        pointer->mutateType(rawPointerTy);
      } else if (pointer->getType()->isMMArrayPointerTy()) {
        _isMMArrayPtr = true;
        rawPointerTy = pointer->getType()->getMMArrayPtrInnerPtrTy();
        pointer->mutateType(rawPointerTy);
      } else {
        rawPointerTy = originalPointerTy;
      }
    }
  }

  // Return true if this Address represents a _MM_ptr.
  bool isMMPtr() const { return _isMMPtr; }

  // Return true if this Address represents a _MM_array_ptr.
  bool isMMArrayPtr() const { return _isMMArrayPtr; }

  //  Set the pointer type to be the inner pointer type of a _MM_ptr
  //  or a _MM_array_ptr.
  void mutatePointerType() {
    if (isMMPtr() || isMMArrayPtr()) Pointer->mutateType(rawPointerTy);
  }

  // Restore the original _MM_ptr or _MM_array type.
  void restoreMMPtrType() { Pointer->mutateType(originalPointerTy); }

  static Address invalid() { return Address(nullptr, CharUnits()); }
  bool isValid() const { return Pointer != nullptr; }

  llvm::Value *getPointer() const {
    assert(isValid());
    return Pointer;
  }

  /// Return the type of the pointer value.
  llvm::PointerType *getType() const {
    llvm::Type *pointerTy = getPointer()->getType();
    if (pointerTy->isMMPointerTy()) {
      // Checked C: extract the inner pointer inside an _MM_ptr.
      return pointerTy->getMMPtrInnerPtrTy();
    }

    return llvm::cast<llvm::PointerType>(getPointer()->getType());
  }

  /// Return the type of the values stored in this address.
  ///
  /// When IR pointer types lose their element type, we should simply
  /// store it in Address instead for the convenience of writing code.
  llvm::Type *getElementType() const {
    return getType()->getElementType();
  }

  /// Return the address space that this address resides in.
  unsigned getAddressSpace() const {
    return getType()->getAddressSpace();
  }

  /// Return the IR name of the pointer value.
  llvm::StringRef getName() const {
    return getPointer()->getName();
  }

  /// Return the alignment of this pointer.
  CharUnits getAlignment() const {
    assert(isValid());
    return Alignment;
  }
};

/// A specialization of Address that requires the address to be an
/// LLVM Constant.
class ConstantAddress : public Address {
public:
  ConstantAddress(llvm::Constant *pointer, CharUnits alignment)
    : Address(pointer, alignment) {}

  static ConstantAddress invalid() {
    return ConstantAddress(nullptr, CharUnits());
  }

  llvm::Constant *getPointer() const {
    return llvm::cast<llvm::Constant>(Address::getPointer());
  }

  ConstantAddress getBitCast(llvm::Type *ty) const {
    return ConstantAddress(llvm::ConstantExpr::getBitCast(getPointer(), ty),
                           getAlignment());
  }

  ConstantAddress getElementBitCast(llvm::Type *ty) const {
    return getBitCast(ty->getPointerTo(getAddressSpace()));
  }

  static bool isaImpl(Address addr) {
    return llvm::isa<llvm::Constant>(addr.getPointer());
  }
  static ConstantAddress castImpl(Address addr) {
    return ConstantAddress(llvm::cast<llvm::Constant>(addr.getPointer()),
                           addr.getAlignment());
  }
};

}

// Present a minimal LLVM-like casting interface.
template <class U> inline U cast(CodeGen::Address addr) {
  return U::castImpl(addr);
}
template <class U> inline bool isa(CodeGen::Address addr) {
  return U::isaImpl(addr);
}

}

#endif
