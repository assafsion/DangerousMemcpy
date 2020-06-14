import cpp
import semmle.code.cpp.models.interfaces.Allocation
import semmle.code.cpp.dataflow.DataFlow


class FfmpegAllocFunction extends AllocationFunction {
  int sizeArg;
  

  FfmpegAllocFunction() {
    exists(string name |
      
      hasGlobalName(name) and
      (
        
        name = "av_malloc" and sizeArg = 0
        or
        
        name = "av_mallocz" and sizeArg = 0
        or

        name = "av_buffer_alloc" and sizeArg = 0
        or

        name = "av_realloc" and sizeArg = 1
        or

        name = "av_fast_realloc" and sizeArg = 1
        
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

}

class FfmpegCallocFunction extends AllocationFunction {
  int sizeArg;
  int multArg;

  FfmpegCallocFunction() {
    exists(string name |
      hasGlobalName(name) and
      (
        name = "av_malloc_array" and sizeArg = 1 and multArg = 0
        or

        name = "av_mallocz_array" and sizeArg = 1 and multArg = 0
        or
        
        name = "av_calloc" and sizeArg = 1 and multArg = 0
      )
    )
  }

  override int getSizeArg() { result = sizeArg }

  override int getSizeMult() { result = multArg }
}


/**
 * An allocation expression that is a function call, such as call to `malloc`.
 */
class CallAllocationExpr extends AllocationExpr, FunctionCall {
  AllocationFunction target;

  CallAllocationExpr() {
    target = getTarget() and
    // realloc(ptr, 0) only frees the pointer
    not (
      exists(target.getReallocPtrArg()) and
      getArgument(target.getSizeArg()).getValue().toInt() = 0
    )
  }


  
  override Expr getSizeExpr() { result = getArgument(target.getSizeArg()) }

  override int getSizeMult() {
    // malloc with multiplier argument that is a constant
    result = getArgument(target.getSizeMult()).getValue().toInt()
    or
    // malloc with no multiplier argument
    not exists(target.getSizeMult()) and
    result = 1
  }

  override int getSizeBytes() { result = getSizeExpr().getValue().toInt() * getSizeMult() }

  override Expr getReallocPtr() { result = getArgument(target.getReallocPtrArg()) }

  override predicate requiresDealloc() { target.requiresDealloc() }
}
