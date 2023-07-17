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

#include "TestDialect.h"
#include "llvm-dialects/Dialect/OpDescription.h"
#include "llvm-dialects/Dialect/OpMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/IR/Intrinsics.h"
#include "gtest/gtest.h"

#include <string>

using namespace llvm;
using namespace llvm_dialects;

[[maybe_unused]] constexpr const char DialectsOpMapBasicTestsName[] =
    "DialectsOpMapBasicTests";

TEST(DialectsOpMapBasicTestsName, CoreOpMapContainsTests) {
  OpMap<StringRef> map;

  OpDescription retDesc = OpDescription::fromCoreOp(Instruction::Ret);
  OpDescription brDesc = OpDescription::fromCoreOp(Instruction::Br);
  map[retDesc] = "RetInst";

  EXPECT_TRUE(map.containsCoreOp(Instruction::Ret));
  EXPECT_FALSE(map.containsCoreOp(Instruction::Br));
  EXPECT_EQ(map[retDesc], "RetInst");

  map[brDesc] = "BrInst";
  EXPECT_EQ(map[retDesc], "RetInst");
  EXPECT_TRUE(map.containsCoreOp(Instruction::Br));
  EXPECT_EQ(map[brDesc], "BrInst");
}

TEST(DialectsOpMapBasicTestsName, IntrinsicOpMapContainsTests) {
  OpMap<StringRef> map;

  OpDescription memCpyDesc = OpDescription::fromIntrinsic(Intrinsic::memcpy);
  OpDescription memMoveDesc = OpDescription::fromIntrinsic(Intrinsic::memmove);
  map[memCpyDesc] = "MemCpy";

  EXPECT_TRUE(map.containsIntrinsic(Intrinsic::memcpy));
  EXPECT_FALSE(map.containsIntrinsic(Intrinsic::memmove));
  EXPECT_EQ(map[memCpyDesc], "MemCpy");

  map[memMoveDesc] = "MemMove";
  EXPECT_EQ(map[memMoveDesc], "MemMove");
  EXPECT_TRUE(map.containsIntrinsic(Intrinsic::memmove));
  EXPECT_EQ(map[memMoveDesc], "MemMove");
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapContainsTests) {
  OpMap<StringRef> map;
  const OpDescription sampleDesc = OpDescription::get<test::DialectOp1>();

  map[OpDescription::get<test::DialectOp1>()] = "Hello";

  EXPECT_TRUE(map.contains<test::DialectOp1>());
  EXPECT_TRUE(map.contains(sampleDesc));
  EXPECT_FALSE(map.contains<test::DialectOp2>());
  EXPECT_EQ(map.findOrConstruct<test::DialectOp1>(), "Hello");

  map[OpDescription::get<test::DialectOp2>()] = "World";
  map.findOrConstruct<test::DialectOp1>() = "DialectOp1";

  EXPECT_TRUE(map.contains<test::DialectOp2>());
  EXPECT_EQ(map.findOrConstruct<test::DialectOp1>(), "DialectOp1");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp2>(), "World");

  map.findOrConstruct<test::DialectOp3>("DialectOp3");
  EXPECT_TRUE(map.contains<test::DialectOp3>());
  EXPECT_EQ(map.findOrConstruct<test::DialectOp3>(), "DialectOp3");
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapfindOrConstructTests) {
  OpMap<StringRef> map;
  map.findOrConstruct<test::DialectOp1>("Hello");
  map.findOrConstruct<test::DialectOp2>("World");
  map.findOrConstruct<test::DialectOp3>("DO3");

  EXPECT_EQ(static_cast<int>(map.size()), 3);
  EXPECT_EQ(map.findOrConstruct<test::DialectOp1>(), "Hello");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp2>(), "World");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp3>(), "DO3");
  map.findOrConstruct<test::DialectOp3>("DO3_Override");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp3>(), "DO3_Override");
  map.erase<test::DialectOp3>();
  EXPECT_EQ(static_cast<int>(map.size()), 2);
  EXPECT_FALSE(map.contains<test::DialectOp3>());

  OpMap<std::string> movableMap;
  // Check if passing a rvalue invokes the move overload.
  std::string testStr = "Test";
  movableMap.findOrConstruct<test::DialectOp1>(
      std::forward<std::string>(testStr));
  EXPECT_EQ(testStr, "");
  movableMap.erase<test::DialectOp1>();

  // Check if passing a const lvalue reference invokes the copy overload of the
  // underlying vector.
  const std::string testStr2 = "Test";
  movableMap.findOrConstruct<test::DialectOp1>(testStr2);
  EXPECT_EQ(testStr2, "Test");
  EXPECT_EQ(testStr2, movableMap.findOrConstruct<test::DialectOp1>());
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapInitializerTests) {
  OpMap<StringRef> map = {
      {{OpDescription::get<test::DialectOp1>(), "Hello"},
       {OpDescription::get<test::DialectOp2>(), "World"},
       {OpDescription::get<test::DialectOp3>(), "DO3"},
       {OpDescription::fromCoreOp(Instruction::Ret), "Ret"},
       {OpDescription::fromIntrinsic(Intrinsic::assume), "Assume"}}};

  EXPECT_TRUE(map.contains<test::DialectOp1>());
  EXPECT_TRUE(map.contains<test::DialectOp2>());
  EXPECT_TRUE(map.contains<test::DialectOp3>());
  EXPECT_TRUE(map.contains(OpDescription::fromCoreOp(Instruction::Ret)));
  EXPECT_TRUE(map.contains(OpDescription::fromIntrinsic(Intrinsic::assume)));

  EXPECT_EQ(map.findOrConstruct<test::DialectOp1>(), "Hello");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp2>(), "World");
  EXPECT_EQ(map.findOrConstruct<test::DialectOp3>(), "DO3");
  EXPECT_EQ(map.findOrConstruct(OpDescription::fromCoreOp(Instruction::Ret)),
            "Ret");
  EXPECT_EQ(
      map.findOrConstruct(OpDescription::fromIntrinsic(Intrinsic::assume)),
      "Assume");

  map[OpDescription::get<test::DialectOp1>()] = "DO1";
  EXPECT_EQ(map.findOrConstruct<test::DialectOp1>(), "DO1");

  map[OpDescription::fromCoreOp(Instruction::Ret)] = "RetInst";
  EXPECT_EQ(map.findOrConstruct(OpDescription::fromCoreOp(Instruction::Ret)),
            "RetInst");
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapEqualityTests) {
  OpMap<StringRef> map = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                           {OpDescription::get<test::DialectOp2>(), "World"},
                           {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  OpMap<StringRef> map2 = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                            {OpDescription::get<test::DialectOp2>(), "World"},
                            {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  EXPECT_EQ(map, map2);

  map.findOrConstruct<test::DialectOp1>() = "DO1";

  EXPECT_NE(map, map2);
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapEqualityOrderingTests) {
  OpMap<StringRef> map = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                           {OpDescription::get<test::DialectOp3>(), "DO3"},
                           {OpDescription::get<test::DialectOp2>(), "World"}}};

  OpMap<StringRef> map2 = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                            {OpDescription::get<test::DialectOp2>(), "World"},
                            {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  EXPECT_EQ(map, map2);
}

TEST(DialectsOpMapBasicTestsName, DialectOpMapEqualityEraseTests) {
  OpMap<StringRef> map = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                           {OpDescription::get<test::DialectOp2>(), "World"},
                           {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  OpMap<StringRef> map2 = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                            {OpDescription::get<test::DialectOp2>(), "World"},
                            {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  EXPECT_EQ(map, map2);

  map.erase<test::DialectOp1>();

  EXPECT_NE(map, map2);
}

TEST(DialectsOpMapBasicTestsName, DialectOpCopyTests) {
  OpMap<StringRef> map = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                           {OpDescription::get<test::DialectOp2>(), "World"},
                           {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  OpMap<StringRef> map2 = map;

  (void)map2;
  EXPECT_EQ(map, map2);
}

TEST(DialectsOpMapBasicTestsName, DialectOpMoveTests) {
  OpMap<StringRef> map = {{{OpDescription::get<test::DialectOp1>(), "Hello"},
                           {OpDescription::get<test::DialectOp2>(), "World"},
                           {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  OpMap<StringRef> map2 = std::move(map);

  EXPECT_TRUE(map.empty());
  EXPECT_NE(map, map2);
}

TEST(DialectsOpMapBasicTestsName, DialectOpIteratorTests) {
  OpMap<StringRef> map = {
      {{OpDescription::get<test::DialectOp1>(), "Hello"},
       {OpDescription::get<test::DialectOp2>(), "World"},
       {OpDescription::fromIntrinsic(Intrinsic::fabs), "fabs"},
       {OpDescription::get<test::DialectOp3>(), "DO3"}}};

  EXPECT_EQ(*map.find(OpDescription::get<test::DialectOp1>()).val(), "Hello");
  EXPECT_EQ(*map.find(OpDescription::get<test::DialectOp2>()).val(), "World");
  EXPECT_EQ(*map.find(OpDescription::fromIntrinsic(Intrinsic::fabs)).val(),
            "fabs");
  EXPECT_EQ(*map.find(OpDescription::get<test::DialectOp3>()).val(), "DO3");
}
