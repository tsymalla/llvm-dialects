/*
***********************************************************************************************************************
*
*  Copyright (c) 2023 Advanced Micro Devices, Inc. All Rights Reserved.
*
*  Permission is hereby granted, free of charge, to any person obtaining a copy
*  of this software and associated documentation files (the "Software"), to deal
*  in the Software without restriction, including without limitation the rights
*  to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
*  copies of the Software, and to permit persons to whom the Software is
*  furnished to do so, subject to the following conditions:
*
*  The above copyright notice and this permission notice shall be included in
*all copies or substantial portions of the Software.
*
*  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
*  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
*  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
*  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
*  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
*  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
*  SOFTWARE.
*
**********************************************************************************************************************/

#pragma once

#include "llvm-dialects/Dialect/Dialect.h"
#include "llvm-dialects/Dialect/OpDescription.h"
#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/IntrinsicInst.h"

#include <tuple>
#include <type_traits>

using namespace llvm;
using namespace llvm_dialects;

namespace {

using DialectOpKey = std::pair<StringRef, bool>;

class DialectOpKVUtils {
public:
  static DialectOpKey getDialectMapKey(const OpDescription &desc) {
    return {desc.getMnemonic(),
            desc.getKind() == OpDescription::Kind::DialectWithOverloads};
  }
};

template <typename ValueT> struct DialectOpKV final {
  DialectOpKey Key;
  ValueT Value;

  bool operator==(const DialectOpKV &other) const {
    return Key.first == other.Key.first && Key.second == other.Key.second &&
           Value == other.Value;
  }

  bool operator==(const OpDescription &desc) const {
    const bool isOverload =
        desc.getKind() == OpDescription::Kind::DialectWithOverloads;
    return Key.first == desc.getMnemonic() && Key.second == isOverload;
  }
};
} // namespace

namespace llvm_dialects {

// Forward declarations.
template <typename ValueT> class OpMap;

template <typename, bool> class OpMapIteratorBase;

// OpMap implements a map-like container that can store core opcodes,
// intrinsics and dialect operations. It provides some lookup functionality for
// these kinds of operations, OpDescriptions and functions as well as
// instructions to simplify working with dialects in scenarios requiring
// association of dialect operations with certain values.
template <typename ValueT> class OpMap final {
  // We don't care about the value type in the @reserve member function,
  // thus we need to make the inners of OpMaps of arbitrary value type
  // accessible to a given OpMap instance.
  template <typename> friend class OpMap;

  friend class OpMapIteratorBase<ValueT, true>;
  friend class OpMapIteratorBase<ValueT, false>;

  using DialectOpKVT = DialectOpKV<ValueT>;

public:
  using iterator = OpMapIteratorBase<ValueT, false>;
  using const_iterator = OpMapIteratorBase<ValueT, true>;

  OpMap() = default;

  // -------------------------------------------------------------
  // Convenience constructor to initialize the OpMap from a set of
  // OpDescription/Value pairs.
  // -------------------------------------------------------------
  OpMap(std::initializer_list<std::pair<OpDescription, ValueT>> vals) {
    for (const std::pair<OpDescription, ValueT> &val : vals)
      findOrConstruct(val.first, val.second);
  }

  // -------------------------------------------------------------
  // Comparison operator overloads.
  // -------------------------------------------------------------
  bool operator==(const OpMap &rhs) const {
    if (m_dialectOps.size() != rhs.m_dialectOps.size())
      return false;

    if (m_coreOpcodes == rhs.m_coreOpcodes &&
        m_intrinsics == rhs.m_intrinsics) {
      // Do a lookup for each vector entry, since both LHS and RHS potentially
      // are in different order.
      for (const auto &dialectOp : rhs.m_dialectOps) {
        if (std::find(m_dialectOps.begin(), m_dialectOps.end(), dialectOp) ==
            m_dialectOps.end())
          return false;
      }

      return true;
    }

    return false;
  }

  bool operator!=(const OpMap &rhs) const { return !(*this == rhs); }

  // -------------------------------------------------------------
  // contains checks if a given op is contained in any of the
  // internal map containers.
  // -------------------------------------------------------------

  bool containsCoreOp(unsigned op) const { return m_coreOpcodes.contains(op); }

  bool containsIntrinsic(unsigned op) const {
    return m_intrinsics.contains(op);
  }

  // Check if the map contains an OpDescription created for a given dialect
  // operation type.
  template <typename OpT> bool contains() const {
    static OpDescription desc = OpDescription::get<OpT>();
    return contains(desc);
  }

  // Check if the map contains an op described by an OpDescription.
  bool contains(const OpDescription &desc) const {
    if (desc.isCoreOp() || desc.isIntrinsic()) {
      assert(desc.getOpcodes().size() == 1 &&
             "OpMap only supports querying of single core opcodes and "
             "intrinsics.");

      const unsigned op = desc.getOpcode();
      return (desc.isCoreOp() && containsCoreOp(op)) ||
             (desc.isIntrinsic() && containsIntrinsic(op));
    }

    for (const DialectOpKVT &dialectOpKV : m_dialectOps) {
      if (dialectOpKV == desc)
        return true;
    }

    return false;
  }

  // -------------------------------------------------------------
  // find returns an iterator that contains info about elements from one of the
  // internal map containers.
  // -------------------------------------------------------------

  // A simple DSL to simplify generating some of the find() overloads

#define GENERATE_FIND_BODY(iterator_t)                                         \
  {                                                                            \
    if (empty())                                                               \
      return end();                                                            \
    iterator_t it(this, arg);                                                  \
    if (it)                                                                    \
      return it;                                                               \
    return end();                                                              \
  }

#define FIND_OVERLOAD(arg_t)                                                   \
  iterator find(arg_t &arg) GENERATE_FIND_BODY(iterator)

#define FIND_CONST_OVERLOAD(arg_t)                                             \
  const_iterator find(const arg_t &arg) const GENERATE_FIND_BODY(const_iterator)

  FIND_OVERLOAD(OpDescription)
  FIND_CONST_OVERLOAD(OpDescription)
  FIND_OVERLOAD(Function)
  FIND_CONST_OVERLOAD(Function)
  FIND_OVERLOAD(Instruction)
  FIND_CONST_OVERLOAD(Instruction)

#undef FIND_CONST_OVERLOAD
#undef FIND_OVERLOAD
#undef GENERATE_FIND_BODY

  // Try to get a pointer to a value for the type of a given function.
  ValueT *findPointer(const Function &func) {
    auto it = find(func);
    if (it)
      return it->second;

    return nullptr;
  }

  // Try to get a pointer to a value for the type of a given instruction.
  ValueT *findPointer(const Instruction &inst) {
    auto it = find(inst);
    if (it)
      return it.second;

    return nullptr;
  }

  // -------------------------------------------------------------
  // findOrConstruct returns a reference to the value stored in any of the
  // internal map containers or constructs a new value.
  // -------------------------------------------------------------

  template <typename OpT> ValueT &findOrConstruct() {
    return findOrConstruct(OpDescription::get<OpT>());
  }

  // Return a reference to the operation described by a given OpDescription.
  // This includes any of the possible operation kinds.
  // Constructs a new entry if the operation was found in neither map.
  ValueT &findOrConstruct(const OpDescription &desc) {
    if (desc.isCoreOp() || desc.isIntrinsic()) {
      assert(desc.getOpcodes().size() == 1 &&
             "OpMap only supports querying of single core opcodes and "
             "intrinsics.");

      const unsigned op = desc.getOpcode();

      if (desc.isCoreOp())
        return m_coreOpcodes[op];

      if (desc.isIntrinsic())
        return m_intrinsics[op];
    }

    if (desc.isDialectOp()) {
      for (DialectOpKVT &dialectOpKV : m_dialectOps) {
        if (dialectOpKV == desc)
          return dialectOpKV.Value;
      }
    }

    // Nothing found. Insert a new dialect operation.
    return insertDialectOp(desc, {});
  }

  // -------------------------------------------------------------
  // Convenience operator[] definitions.
  // -------------------------------------------------------------

  ValueT &operator[](const OpDescription &desc) {
    return findOrConstruct(desc);
  }
  ValueT *operator[](const Function &func) { return findPointer(func); }
  ValueT *operator[](const Instruction &inst) { return findPointer(inst); }

  // -------------------------------------------------------------
  // lookup tries to find whether a given function or instruction
  // can be mapped to any of the entries in the internal map
  // containers.
  // It returns either a default-constructed object if the key
  // was not found or a copy of the contained value.
  // -------------------------------------------------------------

  // Try to lookup a function which is either the callee of an intrinsic call
  // or a dialect operation.
  ValueT lookup(const Function &func) const {
    auto it = find(func);
    if (auto val = it.val(); val)
      return *val;

    return {};
  }

  // Try to lookup an instruction which is either an intrinsic instruction,
  // a dialect operation or a core instruction.
  ValueT lookup(const Instruction &inst) const {
    auto it = find(inst);
    if (auto val = it.val(); val)
      return *val;

    return {};
  }

  // -------------------------------------------------------------
  // Inserts a given Key/Value pair and return a reference or
  // directly return a reference if the key already exists.
  // -------------------------------------------------------------

  ValueT &findOrConstruct(const OpDescription &desc, const ValueT &val) {
    if (desc.isCoreOp() || desc.isIntrinsic()) {
      assert(desc.getOpcodes().size() == 1 &&
             "OpMap: Can only insert a single op at a time.");

      const unsigned op = desc.getOpcode();
      if (desc.isCoreOp()) {
        m_coreOpcodes[op] = val;
        return m_coreOpcodes[op];
      }

      m_intrinsics[op] = val;
      return m_intrinsics[op];
    }

    for (DialectOpKVT &dialectOpKV : m_dialectOps) {
      if (dialectOpKV == desc) {
        dialectOpKV.Value = val;
        return dialectOpKV.Value;
      }
    }

    return insertDialectOp(desc, val);
  }

  template <typename OpT> ValueT &findOrConstruct(const ValueT &val) {
    const OpDescription desc = OpDescription::get<OpT>();
    return findOrConstruct(desc, val);
  }

  template <typename OpT> ValueT &findOrConstruct(ValueT &&val) {
    const OpDescription desc = OpDescription::get<OpT>();
    return findOrConstruct(desc, std::move(val));
  }

  ValueT &findOrConstruct(const OpDescription &desc, ValueT &&val) {
    if (desc.isCoreOp() || desc.isIntrinsic()) {
      assert(desc.getOpcodes().size() == 1 &&
             "OpMap: Can only insert a single op at a time.");

      const unsigned op = desc.getOpcode();
      if (desc.isCoreOp()) {
        m_coreOpcodes[op] = std::move(val);
        return m_coreOpcodes[op];
      }

      m_intrinsics[op] = std::move(val);
      return m_intrinsics[op];
    }

    for (DialectOpKVT &dialectOpKV : m_dialectOps) {
      if (dialectOpKV == desc) {
        dialectOpKV.Value = std::move(val);
        return dialectOpKV.Value;
      }
    }

    return insertDialectOp(desc, std::move(val));
  }

  // -------------------------------------------------------------
  // Erase a given operation from the correct container.
  // -------------------------------------------------------------

  // Erase a given dialect operation.
  template <typename OpT> bool erase() {
    const OpDescription desc = OpDescription::get<OpT>();
    return erase(const_cast<OpDescription &>(desc));
  }

  // Erase all the operations described by a given OpDescription.
  bool erase(OpDescription &desc) {
    iterator it = find(desc);
    if (!it)
      return false;

    return it.erase();
  }

  // -------------------------------------------------------------
  // Reserve a given number of elements for the maps.
  // -------------------------------------------------------------
  void reserve(size_t numCoreOps, size_t numIntrinsics, size_t numDialectOps) {
    m_coreOpcodes.reserve(numCoreOps);
    m_intrinsics.reserve(numIntrinsics);
    m_dialectOps.reserve(numDialectOps);
  }

  template <typename VT> void reserve(const OpMap<VT> &other) {
    m_coreOpcodes.reserve(other.m_coreOpcodes.size());
    m_intrinsics.reserve(other.m_intrinsics.size());
    m_dialectOps.reserve(other.m_dialectOps.size());
  }

  // -------------------------------------------------------------
  // Convenience helpers.
  // -------------------------------------------------------------
  size_t size() const {
    return m_coreOpcodes.size() + m_intrinsics.size() + m_dialectOps.size();
  }

  bool empty() const {
    return m_coreOpcodes.empty() && m_intrinsics.empty() &&
           m_dialectOps.empty();
  }

  // -------------------------------------------------------------
  // Iterator definitions.
  // -------------------------------------------------------------

#define GENERATE_ITERATOR_BODY(iterator_t, name, isEnd)                        \
  {                                                                            \
    if (empty())                                                               \
      return end();                                                            \
    if (!m_coreOpcodes.empty())                                                \
      return iterator_t(this, m_coreOpcodes.name(), isEnd);                    \
    if (!m_intrinsics.empty())                                                 \
      return iterator_t(this, m_intrinsics.name(), isEnd);                     \
    return iterator_t(this, m_dialectOps.name(), isEnd);                       \
  }

#define DEFINE_NONCONST_ITERATOR(name, isEnd)                                  \
  inline iterator name() GENERATE_ITERATOR_BODY(iterator, name, isEnd)

#define DEFINE_CONST_ITERATOR(name, isEnd)                                     \
  inline const_iterator name()                                                 \
      const GENERATE_ITERATOR_BODY(const_iterator, name, isEnd)

  DEFINE_NONCONST_ITERATOR(begin, false)
  DEFINE_NONCONST_ITERATOR(end, true)
  DEFINE_CONST_ITERATOR(begin, false)
  DEFINE_CONST_ITERATOR(end, true)

#undef DEFINE_NONCONST_ITERATOR
#undef DEFINE_CONST_ITERATOR
#undef GENERATE_ITERATOR_BODY

private:
  DenseMap<unsigned, ValueT> m_coreOpcodes;
  DenseMap<unsigned, ValueT> m_intrinsics;
  SmallVector<DialectOpKVT, 1> m_dialectOps;

  ValueT &insertDialectOp(const OpDescription &desc, const ValueT &val) {
    assert(desc.isDialectOp() && "Not a dialect operation!");
    m_dialectOps.push_back({DialectOpKVUtils::getDialectMapKey(desc), val});

    return m_dialectOps.back().Value;
  }

  ValueT &insertDialectOp(const OpDescription &desc, ValueT &&val) {
    assert(desc.isDialectOp() && "Not a dialect operation!");
    m_dialectOps.push_back(
        {DialectOpKVUtils::getDialectMapKey(desc), std::move(val)});
    return m_dialectOps.back().Value;
  }
};

/// A simple iterator operating on the internal data structures of the OpMap. It
/// uses separate storage and stores pointers to the elements of the internal
/// data structures.
/// It should be used with caution, since the iterators get invalidated after
/// inserting or erasing an element.
/// Note that iterating over an OpMap instance never guarantees the order of
/// insertion.
template <typename ValueT, bool isConst> class OpMapIteratorBase final {
  using BaseIteratorT =
      std::conditional_t<isConst,
                         typename DenseMap<unsigned, ValueT>::const_iterator,
                         typename DenseMap<unsigned, ValueT>::iterator>;
  using DialectOpIteratorT = std::conditional_t<
      isConst, typename SmallVectorImpl<DialectOpKV<ValueT>>::const_iterator,
      typename SmallVectorImpl<DialectOpKV<ValueT>>::iterator>;

  using InternalValueT = std::conditional_t<isConst, const ValueT, ValueT>;

  using OpMapT =
      std::conditional_t<isConst, const OpMap<ValueT>, OpMap<ValueT>>;

  friend class OpMapIteratorBase<ValueT, true>;
  friend class OpMapIteratorBase<ValueT, false>;

  class OpMapIteratorState final {
    OpMapIteratorBase &m_iterator;

    enum class IteratorState : uint8_t {
      CoreOp,
      Intrinsic,
      DialectOp,
      Invalid
    };

    bool isCoreOp() const { return m_iterator.m_desc.isCoreOp(); }

    bool isIntrinsic() const { return m_iterator.m_desc.isIntrinsic(); }

    bool isDialectOp() const { return m_iterator.m_desc.isDialectOp(); }

    IteratorState computeCurrentState() {
      const auto isValidIterator = [&](auto it, auto endIt) -> bool {
        return it != endIt;
      };

      if (isCoreOp() &&
          isValidIterator(std::get<BaseIteratorT>(m_iterator.m_iterator),
                          m_iterator.m_map->m_coreOpcodes.end())) {
        return IteratorState::CoreOp;
      }

      if (isIntrinsic() &&
          isValidIterator(std::get<BaseIteratorT>(m_iterator.m_iterator),
                          m_iterator.m_map->m_intrinsics.end())) {
        return IteratorState::Intrinsic;
      }

      if (isDialectOp() &&
          isValidIterator(std::get<DialectOpIteratorT>(m_iterator.m_iterator),
                          m_iterator.m_map->m_dialectOps.end())) {
        return IteratorState::DialectOp;
      }

      return IteratorState::Invalid;
    }

    // Compute a possible next state after iteration.
    IteratorState computeNextState(IteratorState currentState) {
      IteratorState nextState = currentState;

      if (nextState == IteratorState::CoreOp ||
          nextState == IteratorState::Intrinsic) {
        auto peek = std::get<BaseIteratorT>(m_iterator.m_iterator);
        std::advance(peek, 1);

        if (nextState == IteratorState::CoreOp) {
          if (peek == m_iterator.m_map->m_coreOpcodes.end()) {
            if (!m_iterator.m_map->m_intrinsics.empty())
              return IteratorState::Intrinsic;

            nextState = IteratorState::DialectOp;
          }
        }

        if (nextState == IteratorState::Intrinsic) {
          if (peek == m_iterator.m_map->m_intrinsics.end()) {
            if (!m_iterator.m_map->m_dialectOps.empty())
              return IteratorState::DialectOp;

            return IteratorState::Invalid;
          }
        }
      }

      if (nextState == IteratorState::DialectOp) {
        auto peek = std::get<DialectOpIteratorT>(m_iterator.m_iterator);
        std::advance(peek, 1);
        if (peek != m_iterator.m_map->m_dialectOps.end())
          return IteratorState::DialectOp;
      }

      return nextState;
    }

  public:
    OpMapIteratorState(OpMapIteratorBase &iterator) : m_iterator{iterator} {}

    void step() {
      auto currentState = computeCurrentState();
      auto nextState = computeNextState(currentState);

      if (currentState == nextState) {
        switch (currentState) {
        case IteratorState::CoreOp:
        case IteratorState::Intrinsic: {
          auto &it = std::get<BaseIteratorT>(m_iterator.m_iterator);
          ++it;
          if (currentState == IteratorState::CoreOp)
            m_iterator.m_desc = OpDescription::fromCoreOp(it->first);
          else
            m_iterator.m_desc = OpDescription::fromIntrinsic(it->first);

          break;
        }
        case IteratorState::DialectOp: {
          auto &it = std::get<DialectOpIteratorT>(m_iterator.m_iterator);
          ++it;

          m_iterator.m_desc = {it->Key.second, it->Key.first};
          break;
        }

        case IteratorState::Invalid:
          m_iterator.invalidate();
          break;
        }
      } else {
        transitionTo(nextState);
      }
    }

    void transitionTo(IteratorState nextState) {
      if (nextState == IteratorState::Intrinsic) {
        auto newIt = m_iterator.m_map->m_intrinsics.begin();
        m_iterator.m_iterator = newIt;

        m_iterator.m_desc = OpDescription::fromIntrinsic(newIt->first);
      } else if (nextState == IteratorState::DialectOp) {
        auto newIt = m_iterator.m_map->m_dialectOps.begin();
        m_iterator.m_iterator = newIt;

        m_iterator.m_desc = {newIt->Key.second, newIt->Key.first};
      } else {
        m_iterator.invalidate();
      }
    }
  };

public:
  OpMapIteratorBase(OpMapT *map,
                    std::variant<BaseIteratorT, DialectOpIteratorT> it,
                    bool isEnd = false)
      : m_map{map}, m_iterator{it}, m_isEnd{isEnd} {
    assert(!m_map->empty() &&
           "Cannot instantiate OpMapIterator on an empty OpMap!");

    refreshOpDescriptor();
  }

  OpMapIteratorBase(OpMapT *map, const OpDescription &desc)
      : m_map{map}, m_desc{desc} {
    if (desc.isCoreOp() || desc.isIntrinsic()) {
      assert(desc.getOpcodes().size() == 1 &&
             "OpMapIterator only supports querying of single core opcodes and "
             "intrinsics.");

      const unsigned op = desc.getOpcode();

      if (desc.isCoreOp()) {
        m_iterator = map->m_coreOpcodes.find(op);
        if (std::get<BaseIteratorT>(m_iterator) == map->m_coreOpcodes.end())
          invalidate();
      } else {
        m_iterator = map->m_intrinsics.find(op);
        if (std::get<BaseIteratorT>(m_iterator) == map->m_intrinsics.end())
          invalidate();
      }
    } else {
      createFromDialectOp(desc.getMnemonic());
    }
  }

  OpMapIteratorBase(OpMapT *map, const Function &func) : m_map{map} {
    createFromFunc(func);
  }

  // Do a lookup for a given instruction. Mark the iterator as invalid
  // if the instruction is a call-like core instruction.
  OpMapIteratorBase(OpMapT *map, const Instruction &inst) : m_map{map} {
    if (auto *CI = dyn_cast<CallInst>(&inst)) {
      const Function *callee = CI->getCalledFunction();
      if (callee) {
        createFromFunc(*callee);
        return;
      }
    }

    const unsigned op = inst.getOpcode();

    // Construct an invalid iterator.
    if (op == Instruction::Call || op == Instruction::CallBr) {
      invalidate();
      return;
    }

    BaseIteratorT it = m_map->m_coreOpcodes.find(op);
    if (it != m_map->m_coreOpcodes.end()) {
      m_desc = OpDescription::fromCoreOp(op);
      m_iterator = it;
    } else {
      invalidate();
    }
  }

  std::pair<OpDescription, InternalValueT &> operator*() {
    return {m_desc, *val()};
  }

  InternalValueT *val() {
    assert(this->operator bool() &&
           "Trying to call val() on invalid OpMapIterator!");

    if (m_desc.isCoreOp() || m_desc.isIntrinsic())
      return std::addressof(std::get<BaseIteratorT>(m_iterator)->second);

    return std::addressof(std::get<DialectOpIteratorT>(m_iterator)->Value);
  }

  operator bool() const { return !m_isEnd; }

  OpMapIteratorBase &operator++() {
    OpMapIteratorState stateMachine{*this};
    stateMachine.step();

    return *this;
  }

  OpMapIteratorBase &operator++(int) { return this->operator++(); }

  template <bool Proxy = isConst, typename = std::enable_if_t<!Proxy>>
  bool erase() {
    if (m_desc.isCoreOp() || m_desc.isIntrinsic()) {
      assert(m_desc.getOpcodes().size() == 1 &&
             "OpMap only supports erasing of single core opcodes and "
             "intrinsics.");

      const unsigned op = m_desc.getOpcode();

      if (m_desc.isCoreOp())
        return m_map->m_coreOpcodes.erase(op);

      return m_map->m_intrinsics.erase(op);
    }

    // Try to erase the dialect op at last.
    for (size_t I = 0; I < m_map->m_dialectOps.size(); ++I) {
      if (m_map->m_dialectOps[I] == m_desc) {
        DialectOpIteratorT it = m_map->m_dialectOps.begin();
        std::advance(it, I);

        if (it == m_map->m_dialectOps.end())
          return false;

        m_map->m_dialectOps.erase(it);
        return true;
      }
    }

    return false;
  }

protected:
  OpMapT *m_map = nullptr;
  OpDescription m_desc;
  std::variant<BaseIteratorT, DialectOpIteratorT> m_iterator;
  bool m_isEnd = false;

private:
  void invalidate() { m_isEnd = true; }

  void createFromFunc(const Function &func) {
    if (func.isIntrinsic()) {
      m_iterator = m_map->m_intrinsics.find(func.getIntrinsicID());

      if (std::get<BaseIteratorT>(m_iterator) != m_map->m_intrinsics.end()) {
        m_desc = OpDescription::fromIntrinsic(func.getIntrinsicID());
        return;
      }
    }

    createFromDialectOp(func.getName());
  }

  void createFromDialectOp(StringRef funcName) {
    size_t idx = 0;
    bool found = false;
    for (auto &dialectOpKV : m_map->m_dialectOps) {
      const DialectOpKey &key = dialectOpKV.Key;
      if (detail::isOperationDecl(funcName, key.second, key.first)) {
        m_desc = {key.second, key.first};
        auto it = m_map->m_dialectOps.begin();
        std::advance(it, idx);
        m_iterator = it;
        found = true;
        break;
      }

      ++idx;
    }

    if (!found)
      invalidate();
  }

  // Re-construct base OpDescription from the stored iterator.
  void refreshOpDescriptor() {
    if (m_isEnd)
      return;

    if (auto baseIt = std::get_if<BaseIteratorT>(&m_iterator)) {
      auto &unwrapped = *baseIt;
      if (unwrapped != m_map->m_coreOpcodes.end()) {
        m_desc = OpDescription::fromCoreOp(unwrapped->first);
      } else if (unwrapped != m_map->m_intrinsics.end()) {
        m_desc = OpDescription::fromIntrinsic(unwrapped->first);
      }
    } else if (auto dialectOpIt =
                   std::get_if<DialectOpIteratorT>(&m_iterator)) {
      auto &unwrapped = *dialectOpIt;
      if (unwrapped != m_map->m_dialectOps.end())
        m_desc = {unwrapped->Key.second, unwrapped->Key.first};
    } else {
      llvm_unreachable("OpMapIterator: Invalid iterator provided!");
    }
  }
};

} // namespace llvm_dialects
