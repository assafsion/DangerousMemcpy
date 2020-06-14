import cpp
import semmle.code.cpp.controlflow.Guards

import semmle.code.cpp.dataflow.TaintTracking
import DangerousMemcpy
import Config


predicate hasValidGuards(DangerousMemcpy memcpy){
    exists
    (
        GuardCondition gc, BasicBlock bb, Expr left, Expr right | 
        bb = memcpy.getBasicBlock()
        and
        gc.controls(bb, _)
        and
        exists
        (
            boolean enterBlock | 
            gc.ensuresLt(left, right, _, bb, enterBlock)
            and if enterBlock = true
                then forall
                    (
                        Variable v | v = memcpy.getMemcpyLengthVars().getTarget() | 
                        memcpy.getMemcpyLengthVars().getTarget() = left.getAChild*().(VariableAccess).getTarget()
                    )
                else forall
                    (
                        Variable v | v = memcpy.getMemcpyLengthVars().getTarget() | 
                        memcpy.getMemcpyLengthVars().getTarget() = right.getAChild*().(VariableAccess).getTarget()
                    )
        )
        or
        (
            gc.ensuresEq(left, right, _, bb, true)
            and
            forall(Variable v | v = memcpy.getMemcpyLengthVars().getTarget() | v = gc.getAChild*().(VariableAccess).getTarget())
        )
    )
}


// from DangerousMemcpy memcpy, VariableAccess allocSizeVar, VariableAccess memcpyLengthVar
// where
//     not hasValidGuards(memcpy)
//     and
//     allocSizeVar = memcpy.getAllocSizeVars()  and memcpyLengthVar = memcpy.getMemcpyLengthVars()
//     and
//     (
//         if allocSizeVar.getTarget() = memcpyLengthVar.getTarget()
//         then 
//             if exists(PointerFieldAccess v | v = allocSizeVar)
//             then not (globalValueNumber(allocSizeVar.(PointerFieldAccess))) = globalValueNumber(memcpyLengthVar.(PointerFieldAccess))
//             else not (globalValueNumber(allocSizeVar) = globalValueNumber(memcpyLengthVar))
//         else none()
//     )
// select memcpy.getLocation(), allocSizeVar

from PointerFieldAccess va, FunctionCall memcpy
where va.getEnclosingFunction().hasName("decode_slice")
and memcpy.getTarget().hasName("memcpy") and memcpy.getEnclosingFunction().hasName("decode_slice")
and exists(PointerFieldAccess memcpy_length | memcpy_length = memcpy.getArgument(2).getAChild*()
and globalValueNumber(memcpy_length) = globalValueNumber(va))
select memcpy, va