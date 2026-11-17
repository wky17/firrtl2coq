# LoFIRRTL 周期执行接口

`src/LoCircuit.v` 提供 `LoCircuit.LoCircuit.run_circuit`。它复用旧
`LoFirrtl` 的表达式求值，但重新组织周期调度与状态提交，不直接调用旧
`run_module`。旧函数混合当前/下一状态，不能直接提供本接口的状态边界。

```coq
run_circuit : fcircuit VarOrder.T ->
  seq (VarOrder.T * seq bits) -> option execution
```

- `Fcircuit top modules` 中的 `top` 必须是顶层模块标识。
- 第二个参数是 `(输入端口标识, 输入序列)` 列表。输入必须齐全、无重复、
  等长，每个值的位宽须等于端口声明位宽；不允许额外输出端口项。
- 每项是一个完整周期的上升沿采样。每个 Clock 输入在每项中填写
  `[::true]`，不需要交替提供低/高电平。所有模块按同一个周期边界运行。
  派生时钟若在采样点不是高电平会被拒绝；这不是多时钟事件仿真器。
- 首先强制装载寄存器声明的复位值，`NRst` 寄存器初始化为零，内存及同步
  读输出初始化为零。这是显式选定的模拟初始条件，不是硬件内存自动复位
  的保证。复位条件和值目前只能依赖模块输入和常量；初始化使用首项输入，
  空序列使用零数据输入。后续周期仍根据实际复位条件更新寄存器。
- 输入序列为空时，每个输入端口仍需列出，其序列为 `[::]`。
  结果为复位后的状态，`cycles_executed = 0`。
- 无输入端口的电路无法从空端口表推断运行周期数，此接口默认执行零周期。

`Some result` 表示执行成功。`None` 表示输入非法、结构错误、依赖无法解算
或用了不支持的语义；当前接口不区分具体错误原因。

## 读取结果

`final_state result` 是 `(实例路径, module_state)` 列表。顶层路径为 `[::]`，
子实例路径为 `[::iid]`，嵌套路径为 `[::parent_iid; child_iid]`。路径使用实例
标识而不是模块标识；同一模块的多个实例拥有独立状态。

每个 `module_state` 包含：

| 字段 | 含义 |
| --- | --- |
| `current_values` | 最后一项输入下、边沿提交前的信号状态，包含当前可见寄存器值 |
| `current_memories` | 最后一个周期开始时的内存内容 |
| `next_registers` | 最后一项输入采样后，将在下一周期使用的寄存器值 |
| `next_memories` | 最后一个边沿写入后的内存内容 |
| `next_reads` | 同步内存读端口在下一周期使用的数据 |

下一周期的组合输出依赖下一项输入，因此没有对未知未来输入再运行一遍。
例如寄存器复位为 5，连续输入 11、22：最终当前寄存器/输出为 11，下一
寄存器值为 22。内存写掩码为零时保留原地址内容。

可在 Coq 中执行仓库提供的示例：

```coq
From firrtl Require Import LoCircuit TestLoCircuit.
Import LoCircuit.LoCircuit.

Compute observe reg_circuit reg_inputs 3.       (* Some 11 *)
Compute observe_next reg_circuit reg_inputs 2.  (* Some 22 *)

Definition demo_result := run_circuit reg_circuit reg_inputs.
Definition demo_top :=
  match demo_result with
  | Some result => state_at [::] (final_state result)
  | None => None
  end.
```

## 支持范围

支持显式正位宽 UInt/SInt、Clock、AsyncReset，常见表达式、wire/node、单驱动
连接、寄存器、非递归的多层实例，以及读延迟 0/1、写延迟 1、`old`
read-under-write 的内存。实例端口表须与被实例化模块的端口表在顺序、方向、
类型上对应。不同实例的内部局部标识可以相同。

当前拒绝 external module、when/stop 执行、隐式位宽、组合环、重复
声明/驱动、不支持的内存参数、越界访问，以及同一周期多个有效写端口写同一
地址。这是可执行子集，不是全部 LoFIRRTL 的规范实现，也没有声称对官方规范
给出完整正确性证明。

`src/TestLoCircuit.v` 使用 `vm_compute; reflexivity` 检查真实求值结果，涵盖
复位、寄存器、异步复位、多实例/嵌套实例隔离、当前/下一内存、写掩码、同步
读延迟以及非法输入拒绝。
