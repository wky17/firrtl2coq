Installation
============

* [Coq](https://coq.inria.fr) 8.16.0 
* [MathComp](https://github.com/math-comp/math-comp) 1.15.0
* [OCaml]                   4.14.2

git pull
cd firrtl2coq
coq_makefile -f _CoqProject -o Makefile
make
make成功后，应当可以编译 TestAdder.v，是一个coq语法的firrtl电路示例。

cd ocaml
dune build
./_build/default/hipparser.exe ./demo/FormalSimple.fir
可以看到目前OCaml中对firrtl示例FormalSimple.fir parse后，按自定义方式打印出来的语法树。
我们要做的其实就是修改 src/ocaml/hiparser/ast.ml 中的 pp_fcircuit 函数，使得其打印出来的语法符合 TestAdder.v 这种coq可读的形式。
可执行解析器+打印器的调用入口在 src/ocaml/hipparser.ml