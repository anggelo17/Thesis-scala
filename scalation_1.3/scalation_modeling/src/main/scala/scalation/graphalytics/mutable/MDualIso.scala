
//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** @author  Matthew Saltz, John Miller, Ayushi Jain
 *  @version 1.3
 *  @date    Thu Jul 25 11:28:31 EDT 2013
 *  @see     LICENSE (MIT style license file).
 */

package scalation.graphalytics.mutable

import java.io.{BufferedWriter, FileWriter}

import scala.collection.mutable.Map
import scala.collection.mutable.{Set => SET}
import scala.reflect.ClassTag
import scalation.graphalytics.mutable.{ExampleMGraphS => EX_GRAPH}
import scalation.util.time

//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `MDualIso` class provides an implementation for Subgraph Isomorphism
 *  that uses Dual Graph Simulation for pruning.
 *  @param g  the data graph  G(V, E, l)
 *  @param q  the query graph Q(U, D, k)
 */
class MDualIso [TLabel: ClassTag] (g: MGraph [TLabel], q: MGraph [TLabel])
      extends GraphMatcher (g, q)
{
    private val duals        = new MDualSim(g, q)         // object for Dual Simulation algorithm
    private var t0           = 0.0                         // start time for timer
    private var matches      = SET [Array [SET [Int]]] ()  // initialize matches to empty
    private var noBijections = true                        // no results yet
    private var limit        = 1000000                     // limit on number of matches

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Set an upper bound on the number matches to allow before quitting.
     *  @param _limit  the number of matches before quitting
     */
    def setLimit (_limit: Int) { limit = _limit }

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Apply the Dual Subgraph Isomorphism algorithm to find subgraphs of data
     *  graph 'g' that isomorphically match query graph 'q'.  These are represented
     *  by a set of single-valued bijections {'psi'} where each 'psi' function
     *  maps each query graph vertex 'u' to a data graph vertices 'v'.
     */
    override def bijections (): SET [Array [Int]] =
    {
        matches = SET [Array [SET [Int]]] ()               // initialize matches to empty
        val phi = duals.feasibleMates ()                   // initial mappings from label match
        saltzDualIso (duals.saltzDualSim (phi), 0)         // recursively find all bijections
        val psi = simplify (matches)                       // pull bijections out matches
        noBijections = false                               // results now available
        psi                                                // return the set of bijections
    } // bijections

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Apply the Dual Subgraph Isomorphism pattern matching algorithm to find
     *  the mappings from the query graph 'q' to the data graph 'g'.  These are
     *  represented by a  multi-valued function 'phi' that maps each query graph
     *  vertex 'u' to a set of data graph vertices '{v}'.
     */
    def mappings (): Array [SET [Int]] = 
    {
        var psi: SET [Array [Int]] = null              // mappings from Dual Simulation
        if (noBijections) psi = bijections ()          // if no results, create them
        merge (psi)                                    // merge bijections to create mappings
    } // mappings

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Return the count of the number of matches.
     */
    def numMatches (): Int = matches.size

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Refine the mappings 'phi' using the Dual Subgraph Isomorphism algorithm.
     *  Enumerate bijections by using an Ullmann-like recursion that uses Dual
     *  Graph Simulation for pruning.
     *  @param phi    array of mappings from a query vertex u_q to { graph vertices v_g }
     *  @param depth  the depth of recursion
     */
    private def saltzDualIso (phi: Array [SET [Int]], depth: Int)
    {
        if (depth == q.size) {
            if (! phi.isEmpty) {
                matches += phi
                if (matches.size % CHECK == 0) println ("dualIso: matches so far = " + matches.size)
            } // if
        } else if (! phi.isEmpty) {
            for (i <- phi (depth) if (! contains (phi, depth, i))) {
                val phiCopy = phi.map (x => x)                           // make a copy of phi
                phiCopy (depth) = SET [Int] (i)                          // isolate vertex i
                if (matches.size >= limit) return                        // quit if at LIMIT
                saltzDualIso (duals.saltzDualSim (phiCopy), depth + 1)   // solve recursively for the next depth
            } // for
        } // if
    } // saltzDualIso

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Determine whether vertex 'j' is contained in any 'phi(i)' for the previous depths.
     *  @param phi    array of mappings from a query vertex u_q to { graph vertices v_g }
     *  @param depth  the current depth of recursion
     *  @param j      the vertex j to check
     */
    private def contains (phi: Array [SET [Int]], depth: Int, j: Int): Boolean =
    {
        for (i <- 0 until depth if phi(i) contains j) return true
        false
    } // contains

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Create an array to hold matches for each vertex 'u' in the query graph
     *  'q' and initialize it to contain all empty sets.  Then for each bijection,
     *  add each element of the bijection to its corresponding match set.
     *  @param psi  the set of bijections
     */
    private def merge (psi: SET [Array [Int]]): Array [SET [Int]] =
    {
        val matches = Array.ofDim [SET [Int]] (q.size).map (_ => SET [Int] ())
        for (b <- bijections; i <- b.indices) matches(i) += b(i)
        matches
    } // merge

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Pull the bijections out of the complete match set.
     *  @param matches  the complete match set embedding all bijections
     */
    private def simplify (matches: SET [Array [SET [Int]]]): SET [Array [Int]] =
    {
        matches.map (m => m.map (set => set.iterator.next))
    } // simplify

} // MDualIso class


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `MDualIsoTest` object is used to test the `MDualIso` class.
 *  > run-main scalation.graphalytics.mutable.DualIsoTest
 */
object MDualIsoTest extends App
{
    val g = EX_GRAPH.g1
    val q = EX_GRAPH.q1

    println (s"g.checkEdges = ${g.checkEdges}")
    g.printG ()
    println (s"q.checkEdges = ${q.checkEdges}")
    q.printG ()

    val matcher = new MDualIso (g, q)                  // Dual Subgraph Isomorphism Pattern Matcher
    val psi = time { matcher.bijections () }              // time the matcher
    println ("Number of Matches: " + matcher.numMatches)
    for (p <- psi) println (s"psi = ${p.deep}")

} // MDualIsoTest


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `MDualIsoTest2` object is used to test the `MDualIso` class.
 *  > run-main scalation.graphalytics.mutable.DualIsoTest2
 */
object MDualIsoTest2 extends App
{
    val g = EX_GRAPH.g2
    val q = EX_GRAPH.q2

    println (s"g.checkEdges = ${g.checkEdges}")
    g.printG ()
    println (s"q.checkEdges = ${q.checkEdges}")
    q.printG ()

    val matcher = new MDualIso (g, q)                  // Dual Subgraph Isomorphism Pattern Matcher
    val psi = time { matcher.bijections () }              // time the matcher
    println ("Number of Matches: " + matcher.numMatches)
    for (p <- psi) println (s"psi = ${p.deep}")

} // MDualIsoTest2


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `MDualIsoTest3` object is used to test the `MDualIso` class.
 *  > run-main scalation.graphalytics.mutable.DualIsoTest3
 */
object MDualIsoTest3 extends App
{
    val mgGen = new MGraphGen [Int]

    val gSize     = 10000         // size of the data graph
    val qSize     =   10         // size of the query graph

    val nLabels   =  104        // number of distinct vertex labels
    val eLabels   =   10         // number of distinct edge labels

    val gAvDegree =    5         // average vertex out degree for data graph
    val qAvDegree =    3         // average vertex out degree for query graph

    val g = mgGen.genRandomGraph (gSize, nLabels, eLabels, gAvDegree, true, "g")
    val q = mgGen.genBFSQuery (qSize, qAvDegree, g, true, "q")

    println (s"q.checkEdges = ${q.checkEdges}")
    q.printG ()

    val matcher = new MDualIso (g, q)                  // Dual Subgraph Isomorphism Pattern Matcher
    val startTime = System.currentTimeMillis()
    val psi = time { matcher.bijections () }              // time the matcher
    val totaltime=System.currentTimeMillis()-startTime
    println("total time="+totaltime)
    println ("Number of Matches: " + matcher.numMatches)

      val output = new BufferedWriter(new FileWriter("MDualIso.csv",true));  //clears file every time
      output.append(gSize+","+nLabels+","+totaltime+","+matcher.numMatches()+","+qSize+","+qAvDegree+"\n");
      output.close();

    for (p <- psi) println (s"psi = ${p.deep}")

    val matcherCAR = new MDualIsoCAR (g, q)                  // Dual Subgraph Isomorphism Pattern Matcher
    val startTimeCAR = System.currentTimeMillis()
    val psiCAR = time { matcherCAR.bijections () }              // time the matcher
    val totaltimeCAR=System.currentTimeMillis()-startTimeCAR
    println("total time="+totaltimeCAR)
    println ("Number of Matches: " + matcherCAR.numMatches)

    val outputCAR = new BufferedWriter(new FileWriter("MDualIsoCAR.csv",true));  //clears file every time
    outputCAR.append(gSize+","+nLabels+","+totaltimeCAR+","+matcherCAR.numMatches()+","+qSize+","+qAvDegree+"\n");
    outputCAR.close();

    for (p <- psiCAR) println (s"psi = ${p.deep}")




} // MDualIsoTest3

