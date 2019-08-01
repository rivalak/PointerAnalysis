# 程序分析 课程大作业报告

## 一、jar包测试方法

在project路径下执行
`java -jar analyzer.jar ./code test.FieldSensitivity`

## 二、算法主要设计思想及代码实现

1. 在`project/PointerAnalysisByTH/src/core/`目录中基于 **SOOT** 框架实现了一个 **Anderson** 风格的指针分析算法，即基于约束(constraint-based)或基于子集(subset-based)的指针分析方法
2. `Anderson.java`中实现`class ClassFieldsPointSet{}`和`class AllClassesWithFields{}`类来实现域敏感分析。维护两个Map: `Map<SootField, HashSet<Local> > fieldsPointSet;`和`Map<Local, ClassFieldsPointSet> allClasses;`实现Base到Field到Field指向集的映射。
3. `WholeProgramTransformer.java`中对全程序运行`"-p", "cg.spark", "enabled:true", "-p", "wjtp.mypta", "enabled:true"`的pack进行全程序分析，这里是**Jimple**格式的。通过把__benchmark.java__和__A.java__等测试程序转换成Jimple格式分析程序特性，对其中涉及到的SootMethod或者Unit等进行分析。
4. 分析难点： 流敏感分析、域敏感分析
5. 数据流分析框架：
    1. 正向分析
    2. 半格元素：一个字典集合，每个键代表一个变量，值为该变量可能指向的内存位置集合
    3. 交汇操作：并
    4. 变换函数：
        1. Benchmark.alloc(id): 获取id作为下一个new语句的内存位置
        2. Benchmark.test(testcnt,variable):在当前的半格元素中查找variable，找到即打印其可能指向的位置；并将答案记录下来，若答案集中已经存在该变量，则合并其位置集
        3. New语句：在当前的半格元素中新建一个键值对，将变量名作为 key，将之前获取的id初始化为该变量可能指向的位置集合
        4. 赋值语句：存在几种情况，a = b, a.f = b, a.f = b.f  
            * kill 集合是左值对应的内存位置集，gen 集合是右值对应的内存位置集
            * 若右值是域 `base.field`，此时的 gen：先求出 base 所指向的内存位置（如[1,2]），查询当前集合中是否有 1.f,2.f 的位置，若存在则加入 gen 中
            * 若左值是域`base.field`，此时的 kill：同样先求出 base 所指向的内存位置，查询当前集合中是否有该域的位置，若存在则加入 kill 中
            * 执行半格元素的并操作

## References

[Soot 使用简要记录](https://blog.csdn.net/Rivalak/article/details/96829889<Paste>)  
