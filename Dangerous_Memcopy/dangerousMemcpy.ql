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


from DangerousMemcpy memcpy, VariableAccess allocSizeVar, VariableAccess memcpyLengthVar
where
    not hasValidGuards(memcpy)
    and
    allocSizeVar = memcpy.getAllocSizeVars()  and memcpyLengthVar = memcpy.getMemcpyLengthVars()
    and
    (
        if allocSizeVar.getTarget() = memcpyLengthVar.getTarget()
        then not (globalValueNumber(allocSizeVar) = globalValueNumber(memcpyLengthVar))
        else 
            (
                (
                    memcpy.getMemcpyLengthVars().getTarget() = memcpy.getAffectingVarOnAlloc().getTarget()
                    and
                    not globalValueNumber(memcpy.getMemcpyLengthVars()) = globalValueNumber(memcpy.getAffectingVarOnAlloc())
                )
                or
                (
                    not memcpy.getMemcpyLengthVars().getTarget() = memcpy.getAffectingVarOnAlloc().getTarget()
                    and
                    (
                        (
                            memcpy.getAffectingVarOnMemcpyLength().getTarget() = memcpy.getAffectingVarOnAlloc().getTarget()
                            and
                            not globalValueNumber(memcpy.getAffectingVarOnMemcpyLength()) = globalValueNumber(memcpy.getAffectingVarOnAlloc())
                        )
                        or not memcpy.getAffectingVarOnMemcpyLength().getTarget() = memcpy.getAffectingVarOnAlloc().getTarget()
                    )
                )
            )
        )

select memcpy.getLocation(), memcpy.getMemcpyLengthVars()

