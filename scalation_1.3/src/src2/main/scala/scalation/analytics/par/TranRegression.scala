
//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** @author  John Miller
 *  @version 1.3
 *  @date    Sun Jan 18 15:06:16 EST 2015
 *  @see     LICENSE (MIT style license file).
 */

package scalation.analytics.par

import math.log

import scalation.linalgebra.VectoD
import scalation.linalgebra.par.{MatrixD, VectorD}
import scalation.math.FunctionS2S
import scalation.plot.Plot
import scalation.util.{Error, time}

import scalation.analytics.Predictor
import scalation.analytics.RegTechnique._

//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `TranRegression` class supports transformed multiple linear regression.
 *  In this case, 'x' is multi-dimensional [1, x_1, ... x_k].  Fit the parameter
 *  vector 'b' in the transformed regression equation
 *  <p>
 *      transform (y)  =  b dot x + e  =  b_0 + b_1 * x_1 +  b_2 * x_2 ... b_k * x_k + e
 *  <p>
 *  where 'e' represents the residuals (the part not explained by the model) and
 *  'transform' is the function (defaults to log) used to transform the response vector 'y'.
 *  Use Least-Squares (minimizing the residuals) to fit the parameter vector
 *  <p>
 *      b  =  x_pinv * y
 *  <p>
 *  where 'x_pinv' is the pseudo-inverse.
 *  @see www.ams.sunysb.edu/~zhu/ams57213/Team3.pptx
 *  @param x          the design/data matrix
 *  @param y          the response vector
 *  @param transform  the transformation function (defaults to log)
 *  @param technique  the technique used to solve for b in x.t*x*b = x.t*y
 */
class TranRegression (x: MatrixD, y: VectorD, transform: FunctionS2S = log, technique: RegTechnique = QR)
      extends Predictor with Error
{
    if (x.dim1 != y.dim) flaw ("constructor", "dimensions of x and y are incompatible")

    val yy = y.map (transform)                        // transform the response vector
    val rg = new Regression (x, yy, technique)        // regular multiple linear regression

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Train the predictor by fitting the parameter vector (b-vector) in the
     *  regression equation
     *      y  =  b dot x + e  =  [b_0, ... b_k] dot [1, x_1, x_2 ... x_k] + e
     *  using the least squares method.
     */
    def train () { rg.train () }

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Retrain the predictor by fitting the parameter vector (b-vector) in the
     *  multiple regression equation
     *      yy  =  b dot x + e  =  [b_0, ... b_k] dot [1, x_1, x_2 ... x_k] + e
     *  using the least squares method.
     *  @param yy  the new response vector
     */
    def train (yy: VectorD) { rg.train (yy) }

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Return the quality of fit including 'rSquared'.
     */
    def fit: VectorD = rg.fit

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Predict the value of y = f(z) by evaluating the formula y = b dot z,
     *  e.g., (b_0, b_1, b_2) dot (1, z_1, z_2).
     *  @param z  the new vector to predict
     */
    def predict (z: VectoD): Double = rg.predict (z)

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Perform backward elimination to remove the least predictive variable
     *  from the model, returning the variable to eliminate, the new parameter
     *  vector, the new quality of fit.
     */
    def backElim (): Tuple3 [Int, VectoD, VectorD] = rg.backElim ()

    //::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
    /** Compute the Variance Inflation Factor 'VIF' for each variable to test
     *  for multi-collinearity by regressing 'xj' against the rest of the variables.
     *  A VIF over 10 indicates that over 90% of the variance of 'xj' can be predicted
     *  from the other variables, so 'xj' is a candidate for removal from the model.
     */
    def vif: VectorD = rg.vif

} // TranRegression class


//:::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::::
/** The `TranRegressionTest` object tests `TranRegression` class using the following
 *  regression equation.
 *  <p>
 *      log (y)  =  b dot x  =  b_0 + b_1*x_1 + b_2*x_2.
 *  <p>
 */
object TranRegressionTest extends App
{
    val x = new MatrixD ((5, 3), 1.0, 36.0,  66.0,               // 5-by-3 matrix
                                 1.0, 37.0,  68.0,
                                 1.0, 47.0,  64.0,
                                 1.0, 32.0,  53.0,
                                 1.0,  1.0, 101.0)
    val y = VectorD (745.0, 895.0, 442.0, 440.0, 1598.0)
    val z = VectorD (1.0, 20.0, 80.0)

    println ("x = " + x)
    println ("y = " + y)

    val trg = new TranRegression (x, y)
    trg.train ()
    println ("fit = " + trg.fit)

    val yp = trg.predict (z)
    println ("predict (" + z + ") = " + yp)

//  val yyp = trg.predict (x)                             // predict y for several points
//  println ("predict (" + x + ") = " + yyp)
//
//  new Plot (x.col(1), y, yyp)
//  new Plot (x.col(2), y, yyp)

} // TranRegressionTest object

