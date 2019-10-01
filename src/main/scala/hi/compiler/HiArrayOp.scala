// See LICENSE.txt
package ressort.hi.compiler
import ressort.hi


/** Initial representation of HiRes `Operator` Dag after expression parsing
  *
  * The first compiler pass transforms an [[hi.Operator]] into a Dag
  * representation that describes each operator's output as an [[MetaArray]]
  * and each input as another node in the Dag.  It also records other
  * information about how operators can be scheduled onto compute nodes.
  *
  *
  *
  * @param op                   HiRes `Operator` with [[hi.DagOp]] inputs that
  *                             point to other nodes in this Dag.
  *
  * @param materialInputs       For each position in this operator's input list, indicates
  *                             whether that position must be a material array.
  *
  * @param arrayInputs          For each position in this operator's input list, indicates
  *                             whether that position should be nested (array rather than vec)
  *
  * @param dataParallelOutput   This node processes one record at a time, and
  *                             could be treated in parallel (vectorized).
  *
  * @param streamingOutput      This node can produce one output record at a time,
  *                             and is not blocking.
  *
  * @param blockingOutput       This node must finish processing all its inputs
  *                             before any of its outputs may be used.
  *
  * @param controlsOutputCursor This node determines the number of output records,
  *                             and when the next is produced.
  *
  * @param controlsChunkCursor  This node advances chunks in a hash-like array with chaining.
  *
  * @param dynamicAllocation    This node sets the size of its output buffer at runtime
  *
  * @param lastLevelLoop      This node requires that a loop be generated for the
  *                           last level (flat array) of its leader accessor, as
  *                           would result from flat array fusion.
  *
  * @param raisesNestingLevel This node increases the degree of nesting in its
  *                           output array by one. ''Note'': the word nesting
  *                           here is in the sense of HiRes arrays
  *
  * @param lowersNestingLevel This node removes one layer of HiRes array
  *                           nesting from its input to its output.
  *
  * @param blockArrayFusion   This node must terminate array fusion at its depth
  *
  * @param arrayNestingChange Number of [[ArrayView]] layers added or subracted by this node
  *
  * @param isNestedReduction  This node exepects an array of arrays as input,
  *                           and shouldn't be applied to sub-arrays in parallel
  *
  * @param isInternalReduction  This operator performs a nested reduction of an ancillary
  *                             data structure (see [[MergeHistograms]] for example).
  *                             (Admittedly, this is kind of a hack.)
  *
  * @param nonFusable This operator must not be included in a fusion
  *
  * @param skipLoopLevels       Numver of innermost loop levels to skip, as the
  *                             relevant code generator will emit them instead.    
  *
  * @param skipElaboration      Don't generate any loops for this operator.
  */
case class HiArrayOp(
    typed:                hi.TypedHiResOp,
    materialInputs:       List[Boolean],
    arrayInputs:          List[Boolean],
    dataParallelOutput:   Boolean = false,
    streamingOutput:      Boolean = false,
    blockingOutput:       Boolean = false,
    controlsOutputCursor: Boolean = false,
    controlsChunkCursor:  Boolean = false,
    dynamicAllocation:    Boolean = false,
    lastLevelLoop:        Boolean = true,
    raisesNestingLevel:   Boolean = false,
    lowersNestingLevel:   Boolean = false,
    blockArrayFusion:     Boolean = false,
    arrayNestingChange:   Int = 0,
    isNestedReduction:    Boolean = false,
    isInternalReduction:  Boolean = false,
    nonFusable:           Boolean = false,
    skipLoopLevels:       Int = 0,
    skipElaboration:      Boolean = false) {

  assert(streamingOutput || !dataParallelOutput)
  assert(!blockingOutput || (!streamingOutput && !dataParallelOutput))
  assert(!(streamingOutput && !dataParallelOutput && !controlsOutputCursor))

  def op = typed.o
  def hiOp = op
}
