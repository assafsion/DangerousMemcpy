import cpp
import Utils
// Change here the memory library if wrappers exists in project
import MemMangementLibraries.FFmpegMemory
import semmle.code.cpp.dataflow.TaintTracking



class MyConfig extends TaintTracking::Configuration{
    MyConfig() {this = "MyConfig"}

    override predicate isSource(DataFlow::Node node){
        exists(
            CallAllocationExpr alloc_foo | 
            (
                node.asExpr() = alloc_foo
                and not alloc_foo.getFile().toString().matches("%mem.c%")
            )
        )
    }


    override predicate isSink(DataFlow::Node node){
        exists(
            FunctionCall fc | 
            isMemcpy(fc)
            and
            node.asExpr() = fc.getArgument(0)
        )
    }

}

class TaintedVarConfig extends TaintTracking::Configuration{
TaintedVarConfig() {this = "TaintedVarConfig"}

    override predicate isSource(DataFlow::Node node){
        exists
        (
            VariableAccess va|
            node.asExpr() = va
        )
    }


    override predicate isSink(DataFlow::Node node){
        exists
        (
            Expr e | 
            node.asExpr() = e
        )
    }

}

