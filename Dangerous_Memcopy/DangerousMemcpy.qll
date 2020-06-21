import cpp
import Config
import Utils
import semmle.code.cpp.controlflow.Guards
import semmle.code.cpp.valuenumbering.GlobalValueNumbering



VariableAccess getAllocSizeVariables(CallAllocationExpr alloc){
    result = alloc.getAnArgument().getAChild*()
    and
    isNumber(result.getTarget())
}




class DangerousMemcpy extends FunctionCall{
    
    CallAllocationExpr sourceAlloc;
    VariableAccess lengthVariable;
    VariableAccess taintLengthVariables;
    VariableAccess allocVariable;
    VariableAccess taintAllocVariables;
    GuardCondition guardingCondition;

    DangerousMemcpy(){
        // Is our function call is a memcpy
        isMemcpy(this)

        // Working with variables that are numbers!
        and
        (
            isNumber(lengthVariable.getTarget()) 
            and 
            isNumber(allocVariable.getTarget()) 
            and 
            isNumber(taintAllocVariables.getTarget())
            and
            isNumber(taintLengthVariables.getTarget())
        )
        and

        // Setting lengthVariable to be the 2nd argument in our memcpy
        this.getArgument(2).getAChild*() = lengthVariable
        and
        
        // Set sourceAlloc and allocVariable 
        exists
        (
            DataFlow::PathNode alloc, DataFlow::PathNode memcpy_dst, MyConfig cfg | 

            // link memcpyt_dst to our memcpy first argument
            memcpy_dst.getNode().asExpr() = this.getArgument(0)
            and
            // link our alloc to a memcpy
            cfg.hasFlowPath(alloc, memcpy_dst)
            and
            // link our sourceAlloc to the alloc
            alloc.getNode().asExpr() = sourceAlloc
            and
            // link allocVariable to the variables that define the alloc size
            sourceAlloc.getAnArgument().getAChild*() = allocVariable
        )
        and
        
        // Clear all 100% safe memcpy`s using global value numbering
        not (globalValueNumber(this.getArgument(2)) = globalValueNumber(sourceAlloc.getAnArgument()))
        and

        // Set taintAllocVariables
        exists
        (
            DataFlow::PathNode variableFlowToAlloc, DataFlow::PathNode allocSizeNode, TaintedVarConfig taintVarCfg | 

            // link allocSizeNode to the allocation variables
            allocSizeNode.getNode().asExpr() = allocVariable
            and
            // Find all the variables that flow to alloc size node
            taintVarCfg.hasFlowPath(variableFlowToAlloc, allocSizeNode)
            and
            // link our node to taintAllocVariables
            variableFlowToAlloc.getNode().asExpr() = taintAllocVariables
        )
        and

        // Set taintLengthVariables
        exists
        (
            DataFlow::PathNode variableFlowToLength, DataFlow::PathNode memcpy_length, TaintedVarConfig taintVarCfg |

            // link memcpy_length to lengthVariable
            memcpy_length.getNode().asExpr() = lengthVariable
            and
            // Find all the variables that affect the memcpy length variable
            taintVarCfg.hasFlowPath(variableFlowToLength, memcpy_length)
            and
            //link variableFlowToLength to taintLengthVariables
            variableFlowToLength.getNode().asExpr() = taintLengthVariables

        )
       


    }

    VariableAccess getMemcpyLengthVars(){
        result = lengthVariable
    }

    VariableAccess getAllocSizeVars(){
        result = allocVariable
    }

    CallAllocationExpr getAllocationFunctions(){
        result = sourceAlloc
    }

    VariableAccess getAffectingVarOnAlloc(){
        result = taintAllocVariables
    }

    VariableAccess getAffectingVarOnMemcpyLength(){
        result = taintLengthVariables
    }

    

    predicate isMemcpyNotGuardedEnough(){
        exists
        (
            BasicBlock bb, GuardCondition gc, Expr left, Expr right | 
            bb = this.getBasicBlock()
            and 
                // No Guards at all - Easy scenario
                (
                    not gc.controls(bb, _)
                    
                )
                // Guard exists - checking the type of the guard and where is the length variable.
                or
                (
                    gc.controls(bb, _)
                    and
                    (
                        (
                            // Condition has the form: x < y and must be true in order for memcpy to execute
                            // Make sure the check dosen`t check the maximum value of the length variable
                            exists
                            (
                                boolean enterBlock | 
                                gc.ensuresLt(left, right, _, bb, enterBlock)
                                and if enterBlock = true
                                    then not lengthVariable.getTarget() = left.getAChild*().(VariableAccess).getTarget()
                                    else  not lengthVariable.getTarget() = right.getAChild*().(VariableAccess).getTarget()
                            )
                            
                        )
                        or
                        (
                            // Meaning guard is from the form of x == y to execute memcpy
                            gc.ensuresEq(left, right, _, bb, true)
                            and
                            // In that case, make sure the length variable is not checked
                            // If it is being checked, it means length must have a specific value => well guraded
                            not 
                            (
                                lengthVariable.getTarget() = gc.getAChild*().(VariableAccess).getTarget()
                            )
                            
                        )
                    )
                )

        )
    }

}