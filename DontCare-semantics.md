# DontCare 的有限符号输入语义

## 核对依据

项目使用 Chisel 3.6.0 / ChiselTest 0.6.0。这里对应的是 ChiselTest 的 formal 后端，而不是 ChiselVerify constrained-random testing 的随机采样器。

- [FIRRTL InvalidToRandomPass](https://github.com/chipsalliance/firrtl/blob/1.6.x/src/main/scala/firrtl/backends/experimental/smt/random/InvalidToRandomPass.scala)：将 `IsInvalid` 转换成具名 `DefRandom` 和连接。
- [DefRandom](https://github.com/chipsalliance/firrtl/blob/1.6.x/src/main/scala/firrtl/backends/experimental/smt/random/DefRandom.scala)：带有类型和时钟的具名任意值来源；未指定时钟时使用全局时钟。
- [ChiselTest v0.6.0 回归](https://github.com/ucb-bar/chiseltest/blob/v0.6.0/src/test/scala/chiseltest/formal/UndefinedValuesTests.scala)：对二位 DontCare，断言其恒等于任意一个固定值都应失败。

## Coq 表示

`src/Semantics_with_memory.v` 中现有正式入口已经采用此模型：

```coq
Definition symbolic_word (width : nat) :=
  { value : bits | size value = width }.
Record formal_inputs := {
  formal_external_inputs : VM.t hvalue;
  formal_symbolic_inputs : symbolic_inputs
}.
```

宽度为 w 的 UInt 任意值可以是 0 到 2^w−1；SInt 使用同样宽度的补码位模式。这里没有均匀分布或随机抽样要求。正式命题全称量化输入流，必须覆盖所有符合假设的选择。

符号来源由实例路径、静态 invalid 语句位置和聚合叶子共同标识。`formal_invalid_policy` 将其构造成真实的 `Gval` / 聚合值。一个周期的所有组合传播轮次与提交共享同一份输入；下一周期可重新指定。复制值保持相关性，独立来源允许不同值。不会因为每次读取而重新抽样。

`generated_legal_trace` 使用 `trace_satisfies` 约束每个已消费周期的设计 assume。位宽之外不添加臆造的范围或稳定性限制；违反 assume 的轨迹不属于证明量化的合法轨迹，但并不要求求值器因此返回 None。

内存初值仍由独立参数选择一次，并随写入更新；不会在每个周期重新选择或在 reset 时统一清零。尚未传播到的值、未初始化寄存器及求值失败也不会自动转换成 DontCare。

## 本次改动与验证

工作区已有上述运行实现，本次核对后保留它，没有再引入一套不同的随机语义。

新增 `src/FormalInputChecks.v` 并接入 `_CoqProject`：

1. 任意满足位宽的向量都能被输入接口表达。
2. 同来源读取一致，位宽由依赖类型强制保证。
3. 真实 Sinvalid 语句经过两轮求值后，两个来源可以不同，同一来源的两个节点副本相等。
4. 下一周期允许给相同来源提供不同值。
5. 当前满足 assume 不能消除历史违例。
6. 不同实例中的相同语句位置可以取不同值，避免错误共享随机源。

七条引理/例子通过 coqc；该模块通过 coqchk -norec 检查。此前转换器经 dune 重新构建并从现有 CoreSoc.hi.fir 生成 Coq，结果与 formal/CoreSoc.v 逐字节相同，因此无需覆盖源文件。

这是显式 DontCare 的建模与回归验证，不是整个 FIRRTL formal 后端的等价性证明。上游同一转换还处理 validif 和除零；本文不据此声称当前实现覆盖了所有隐式未定义行为。CoreSoc 的任意周期断言证明是另外的任务。
