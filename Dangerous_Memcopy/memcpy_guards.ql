import cpp
import semmle.code.cpp.controlflow.Guards

import semmle.code.cpp.dataflow.TaintTracking
import Config

from GuardCondition gc, BasicBlock bb, VariableAccess va, MyConfig cfg, DataFlow::PathNode alloc, FunctionCall memcpy,DataFlow::PathNode memcpy_dst, boolean guardIsEqual, Expr left, Expr right, boolean enterBlock
where 
    cfg.hasFlowPath(alloc, memcpy_dst)
    and
    memcpy.getArgument(0) = memcpy_dst.getNode().asExpr()
    and
    bb = memcpy.getBasicBlock()
    and
    gc.controls(bb, _)
    and
        (
            (
                gc.ensuresLt(left, right, _, bb, enterBlock)
                and
                guardIsEqual = false
            )
            or
            (
                gc.ensuresEq(left, right, _, bb, enterBlock)
                and
                guardIsEqual = true
            )
        )
    
    
    
select memcpy.getLocation() as memcpy_location, gc.getLocation() as guard_location, left.getAChild*() as leftSide, right.getAChild*() as rightSide, guardIsEqual, enterBlock