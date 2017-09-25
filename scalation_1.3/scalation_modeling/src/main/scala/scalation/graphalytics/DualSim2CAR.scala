
//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** @author  Matthew Saltz, John Miller
 *  @version 1.3
 *  @date    Thu Jul 25 11:28:31 EDT 2013
 *  @see     LICENSE (MIT style license file).
 *
 *  Graph Dual Simulation Using Immutable Sets
 */

package scalation.graphalytics

import scala.collection.immutable.{Set => SET}
import scala.reflect.ClassTag
import scalation.graphalytics.mutable.LabelFunctionsCAR.{gChildLabels, gParentLabels, qChildLabels, qParentLabels}
import scalation.graphalytics.mutable.MGraph
import scalation.util.MultiSet

//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `DualSim2` class provides a second implementation for Dual Graph Simulation.
 *  It differs from `DualSim` by not using inverse adjacency sets ('pa') in
 *  order to save space.
 *  @param g  the data graph  G(V, E, l)
 *  @param q  the query graph Q(U, D, k)
 */
class DualSim2CAR[TLabel: ClassTag](g: GraphCAR[TLabel], q: GraphCAR[TLabel])
      extends GraphMatcherCAR (g, q)
{
    private val DEBUG = true                                      // debug flag

  /** The Child labels for the query graph
    */
  private val cLabel = Array.ofDim[MultiSet[TLabel]](q.size)
  for (u <- cLabel.indices) cLabel(u) = qChildLabels(q, u)

  /** The Parent labels for the query graph
    */
  private val pLabel = Array.ofDim[MultiSet[TLabel]](q.size)
  for (u <- pLabel.indices) pLabel(u) = qParentLabels(q, u)

  //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
  /** Apply the Dual Graph Simulation pattern matching algorithm to find the mappings
    * from the query graph 'q' to the data graph 'g'.  These are represented by a
    * multi-valued function 'phi' that maps each query graph vertex 'u' to a
    * set of data graph vertices '{v}'.
    */
  def mappings(): Array[SET[Int]] = DualSimCAR(feasibleMates())

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Apply the Dual Graph Simulation pattern matching algorithm to find the mappings
     *  from the query graph 'q' to the data graph 'g'.  These are represented by a
     *  multi-valued function 'phi' that maps each query graph vertex 'u' to a
     *  set of data graph vertices '{v}'.
     */
   // def mappings (): Array [SET [Int]] = saltzDualSim (feasibleMates ())

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Given the mappings 'phi' produced by the 'feasibleMates' method,
     *  eliminate mappings 'u -> v' when (1) v's children fail to match u's
     *  or (2) v's parents fail to match u's.
     *  @param phi  array of mappings from a query vertex u to { graph vertices v }
     */
    def saltzDualSim (phi: Array [SET [Int]]): Array [SET [Int]] =
    {
        var alter = true
        while (alter) {                                           // check for matching children/parents
            alter = false

            for (u <- qRange; u_c <- q.ch(u)) {                   // for each u in q and its children u_c  
                if (DEBUG) { println (s"for u = $u, u_c = $u_c"); showMappings (phi) }
                var newPhi = SET [Int] ()                         // subset of phi(u_c) having a parent in phi(u)

                for (v <- phi(u)) {                               // data vertex v matching u's label
                    val phiInt = g.ch(v) & phi(u_c)               // children of v contained in phi(u_c)
                    if (phiInt.isEmpty) {
                        phi(u) -= v                               // remove vertex v from phi(u)
                        if (phi(u).isEmpty) return phi            // no match for vertex u => no overall match
                        alter = true
                    } // if
                    // build newPhi to contain only those vertices in phi(u_c) which also have a parent in phi(u)
                    newPhi ++= phiInt
                } // for

                if (newPhi.isEmpty) return phi                    // empty newPhi => no match
                if (newPhi.size < phi(u_c).size) alter = true     // since newPhi is smaller than phi(u_c)

                if (SELF_LOOPS && u_c == u) phi(u_c) &= newPhi else phi(u_c) = newPhi
            } // for

        } // while
        phi
    } // saltzDualSim


    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Given the mappings 'phi' produced by the 'feasibleMates' method,
      * eliminate mappings 'u -> v' when (1) v's children fail to match u's
      * or (2) v's parents fail to match u's.
      *
      * @param phi array of mappings from a query vertex u to { graph vertices v }
      */
     def DualSimCAR(phi: Array[SET[Int]]): Array[SET[Int]] = {
        var alter = true
        var continue = true
        //        while (alter) {                                     // check for matching children and parents
        //            alter = false
        //           // println(qRange+"rangeQ")
        //            // loop over query vertices u, data vertices v in phi(u), and u's children u_c
        //            for (u <- qRange; v <- phi(u); u_c <- q.ch(u); v_c <- g.ch(v)) {
        //                //println("u="+u)
        //                val elab_u2u_c = q.elabel (u, u_c)        // edge label in q for (u, u_c)
        //                val elab_v2v_c = g.elabel (v, v_c)        // edge label in g for (v, v_c)
        //                val chu = cLabel(u)
        //                val chv = gChildLabels(g, v,  u, q.ch(u), phi)
        //                val res = ! (chu ⊆ chv)
        //                val res1 = (elab_u2u_c != elab_v2v_c)
        //                //val hasWild     = hasWildcards (elab_u2u_c)
        //                //val welab_u2u_c = if (hasWild) new Wildcard (elab_u2u_c.asInstanceOf [String]) else null.asInstanceOf [Wildcard]
        //                //val result = (welab_u2u_c =~ (elab_v2v_c).asInstanceOf [String])
        //                val result = !(elab_v2v_c == elab_u2u_c)
        //                println("Child loop")
        //                println(" u = " + u + " , v =  " + v + "  " + res + "  " + res1 + "  " + elab_v2v_c + "  " + elab_u2u_c + "  " + result)
        //
        //                if (DEBUG) println("u : " + u + " v : " + v + " chu : " + chu + " chv : " + chv + " res : " + res)
        //                //if (res || res1)   {
        //                if (res || res1 && result)  {
        //                    phi(u) -= v                             // remove v due to lack of child match
        //                    println("Removed")
        //                    alter  = true
        //                } // if
        //            } //for
        //
        //            // loop over query vertices u, data vertices v in phi(u), and u's parents u_p
        //            for (u <- qRange; v <- phi(u); u_c <- q.ch(u); v_c <- g.ch(v)) {
        //
        //                val elab_u2u_p = q.elabel ((u, u_c))                       // edge label in q for (u, u_c)
        //                val elab_v2v_p = g.elabel ((v, v_c))                       // edge label in g for (v, v_c)
        //                val pau = pLabel(u)
        //                val pav = gParentLabels(g, v, u, q.pa(u), phi)
        //                val res = ! (pau ⊆ pav)
        //                val res1 =  (elab_u2u_p != elab_v2v_p )
        //                //val hasWild     = hasWildcards (elab_u2u_p)
        //                //val welab_u2u_p = if (hasWild) new Wildcard (elab_u2u_p.asInstanceOf [String]) else null.asInstanceOf [Wildcard]
        //                //val result = (welab_u2u_p =~ (elab_v2v_p).asInstanceOf [String])
        //                val result = !(elab_u2u_p == elab_v2v_p)
        //                println("Parent loop")
        //                println(" u = " + u + " , v =  " + v + "  " + res + "  " + res1 + "  " + elab_u2u_p + "  " + elab_v2v_p + "  " + result)
        //
        //                if (DEBUG) println("u : " + u + " v : " + v + " pau : " + pau + " pav : " + pav + " res : " + res)
        //                //if (res || res1)   {
        //                if (res || res1 && result)  {
        //                    phi(u) -= v                             // remove v due to lack of child match
        //                    println("Removed")
        //                    alter  = true
        //                } // if
        //            } //for
        //
        //        } // while
        //        phi

        while (alter) {
            alter = false

            for (u <- qRange) {

                //if (DEBUG) { println (s"for u = $u, u_c = $u_c"); showMappings (phi) }
                val newPhi = SET[Int]() // subset of phi(u_c) having a parent in phi(u)
                //  val elab_u2u_c = q.elabel ((u, u_c))              // edge label in q for (u, u_c)

                for (v <- phi(u)) {
                    // for each v in g image of u
                    //                  val v_c = g.ch(v)                                          // don't filter on edge labels
                    //  val v_c = g.ch(v).filter (elab_u2u_c == g.elabel (v, _))   // filter on edge labels
                    if (DEBUG) println(s"v = $v, u = $u, phi_u = " + phi(u))

                    continue = true


                    val chu = cLabel(u)

                    val chv = gChildLabels(g, v, u, q.ch(u), phi)
                    val res1 = !(chu ⊆ chv)

                    if (res1) {

                        phi(u) -= v
                        if (phi(u).isEmpty) return phi
                        alter= true
                        continue= false

                    }

                    if(continue) {


                        val pau = pLabel(u)

                        val pav = gParentLabels(g, v, u, q.pa(u), phi)
                        val res2 = !(pau ⊆ pav)


                        if (res1 || res2) {
                            phi(u) -= v
                            if (phi(u).isEmpty) return phi
                            alter = true

                        }


                    }


                } // for


            } //for

        } //while

        phi

    }


} // DualSim2 class


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `DualSim2Test` object is used to test the `DualSim2` class.
 *  > run-main scalation.graphalytics.DualSim2Test
 */
object DualSim2CARTest extends App
{
    val g = GraphCARO.g1
    val q = GraphCARO.q1

    println (s"g.checkEdges = ${g.checkEdges}")
    g.printG ()
    println (s"q.checkEdges = ${q.checkEdges}")
    q.printG ()

    (new DualSim2CAR (g, q)).test ("DualSim2")    // Dual Graph Simulation Pattern Matcher

} // DualSim2Test object


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `DualSim2Test2` object is used to test the `DualSim2` class.
 *  > run-main scalation.graphalytics.DualSim2Test2
 */
object DualSim2CARTest2 extends App
{
//    val g = GraphCAR.g2
//    val q = GraphCAR.q2
//
//    println (s"g.checkEdges = ${g.checkEdges}")
//    g.printG ()
//    println (s"q.checkEdges = ${q.checkEdges}")
//    q.printG ()
//
//    (new DualSim2 (g, q)).test ("DualSim2")    // Dual Graph Simulation Pattern Matcher

} // DualSim2Test2 object


//::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `DualSim2Test3` object is used to test the 'DualSim2' class.
 *  > run-main scalation.graphalytics.DualSim2Test3
 */
object DualSim2CARTest3 extends App
{
    val gSize     = 1000         // size of the data graph
    val qSize     =   10         // size of the query graph
    val nLabels   =  100         // number of distinct labels
    val gAvDegree =    5         // average vertex out degree for data graph
    val qAvDegree =    2         // average vertex out degree for query graph

    val g = GraphGen.genRandomGraph (gSize, nLabels, gAvDegree, false, "g")
    val q = GraphGen.genBFSQuery (qSize, qAvDegree, g, false, "q")

    println (s"q.checkEdges = ${q.checkEdges}")
    q.printG ()

    //new DualSim2 (g, q).test ("DualSim2")    // Dual Graph Simulation Pattern Matcher

} // DualSim2Test3 object

