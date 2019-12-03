// See LICENSE.txt
package ressort.compiler

/** Insertion sort code generation parameters
  *
  * @param Use Mux() instead of If?
  * @param Don't gen special code for sizes > maxUnroll
  * @param Threshold below which don't attempt reg alloc
  */
case class InsertionSortConfig(
  genCmov: Boolean=false,
  maxUnroll: Int=0,
  regsThresh: Int=1)

case class RadixPartConfig(
  debug:            Boolean=false,
  useWriteBuffer:   Boolean=true,
  linesz:           Int=64)

case class CompilerConfig(
  isort:          InsertionSortConfig,
  rpart:          RadixPartConfig,
  initBuffers:    Boolean,
  addRestrict:    Boolean,
  arrayFusion:    Boolean,
  vectorFusion:   Boolean,
  blockingJoin:   Boolean,
  cse:            Boolean,
  constProp:      Boolean,
  unpackStructs:  Boolean
)

object CompilerConfig {
  val DefaultConfig = {
    CompilerConfig(
      initBuffers   = false,
      addRestrict   = false,
      arrayFusion   = true,
      vectorFusion  = true,
      blockingJoin  = false,
      cse           = true,
      constProp     = true,
      unpackStructs = true,
      isort         = InsertionSortConfig(),
      rpart         = RadixPartConfig())
  }
}

