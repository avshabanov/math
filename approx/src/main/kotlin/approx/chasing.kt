package approx.chasing

import java.awt.image.BufferedImage
import java.awt.Graphics2D
import java.awt.Color
import javax.imageio.ImageIO
import java.io.File
import java.awt.geom.Point2D

fun drawImg() {
  val image = BufferedImage(800, 600, BufferedImage.TYPE_3BYTE_BGR)
  val g = image.getGraphics();
  if (g !is Graphics2D) {
    throw IllegalStateException("can't get 2D graphics")
  }

  g.setBackground(Color.WHITE)
  g.fillRect(0, 0, 800, 600)
  g.setColor(Color.RED)
  g.drawLine(0, 0, 800, 600)
  g.drawLine(0, 600, 800, 0)

  ImageIO.write(image, "png", File("/Users/alex/Downloads/1.png"))
}

trait ChasingCalc {
  val foxX : Double
  val foxY : Double
  val rabbitX : Double
  val rabbitY : Double
  val maxSteps : Int

  fun move() : Boolean
}

class LinearChasingCalc (
    val foxVelocity: Double = 1.618,
    val rabbitVelocity: Double = 1.0,
    val termDistance : Double = 0.001,
    override val maxSteps : Int = 1000,
    val timeStep : Double = 0.001
) : ChasingCalc {
  override var foxX = 1.0
  override var foxY = 0.0
  override var rabbitX = 0.0
  override var rabbitY = 0.0
  var time = 0.0

  override fun move() : Boolean {
    val dx = rabbitX - foxX
    val dy = rabbitY - foxY
    val dist = Math.sqrt(dx * dx + dy * dy)

    if (dist < termDistance) {
      return false // terminal point
    }

    time += timeStep

    // fox step
    val foxStep = timeStep * foxVelocity
    // fox radial velocity projections
    val distRatio = foxStep / dist
    foxX += dx * distRatio
    foxY += dy * distRatio

    // rabbit step
    val rabbitStep = timeStep * rabbitVelocity
    rabbitX = 0.0
    rabbitY += rabbitStep

    return true
  }
}

class CircChasingCalc (
    val foxVelocity: Double = 2.0,
    val rabbitVelocity: Double = 1.0,
    val termDistance : Double = 0.001,
    override val maxSteps : Int = 1000,
    val timeStep : Double = 0.001,
    val rabbitCircRadius : Double = 1.0,
    val rabbitCenterX : Double = 1.0,
    val rabbitCenterY : Double = 0.0
) : ChasingCalc {
  override var foxX = 10.0
  override var foxY = 0.0
  override var rabbitX = rabbitCenterX + rabbitCircRadius
  override var rabbitY = rabbitCenterY
  var time = 0.0

  val rabbitCircKsiDelta = (timeStep * rabbitVelocity) / rabbitCircRadius
  var rabbitCircKsi = 0.0

  override fun move() : Boolean {
    val dx = rabbitX - foxX
    val dy = rabbitY - foxY
    val dist = Math.sqrt(dx * dx + dy * dy)

    if (dist < termDistance) {
      return false // terminal point
    }

    time += timeStep

    // fox step
    val foxStep = timeStep * foxVelocity
    // fox radial velocity projections
    val distRatio = foxStep / dist
    foxX += dx * distRatio
    foxY += dy * distRatio

    // rabbit step
    rabbitCircKsi += rabbitCircKsiDelta
    rabbitX = rabbitCenterX + rabbitCircRadius * Math.cos(rabbitCircKsi)
    rabbitY = rabbitCircRadius * Math.sin(rabbitCircKsi)

    return true
  }
}

class ChasingPathDrawer(val imageWidth : Int = 520,
                        val imageHeight : Int = 520,
                        val markerSentinel : Int = 100,
                        val trScale : Int = 500,
                        val trX : Int = 10,
                        val trY : Int = 510) {

  fun drawPath(calc : ChasingCalc, targetFile : File) {
    val image = BufferedImage(imageWidth, imageHeight, BufferedImage.TYPE_3BYTE_BGR)
    val g = image.getGraphics();
    if (g !is Graphics2D) {
      throw IllegalStateException("can't get 2D graphics")
    }

    g.setBackground(Color.WHITE)
    g.fillRect(0, 0, imageWidth, imageHeight)

    var step = 0
    var markerCounter = 0
    var counter = 1
    var isTerm = false
    var foxPtX = 0
    var foxPtY = 0

    while (step < calc.maxSteps) {
      val prevFoxX = calc.foxX
      val prevFoxY = calc.foxY
      val prevRabbitX = calc.rabbitX
      val prevRabbitY = calc.rabbitY

      if (!calc.move()) {
        isTerm = true
        break
      }

      if (markerCounter > markerSentinel) {
        markerCounter = 0
        ++counter
      }
      val putMarker = markerCounter == 0

      g.setColor(Color.RED)
      foxPtX = trX + (prevFoxX * trScale).toInt()
      foxPtY = trY - (prevFoxY * trScale).toInt()
      g.drawLine(foxPtX, foxPtY, trX + (calc.foxX * trScale).toInt(), trY - (calc.foxY * trScale).toInt())
      if (putMarker) {
        g.drawOval(foxPtX - 2, foxPtY - 2, 4, 4)
        g.setColor(Color.RED.darker())
        g.drawString(Integer.toString(counter), foxPtX, foxPtY)
      }

      g.setColor(Color.GREEN)
      val rabbitPtX = trX + (prevRabbitX * trScale).toInt()
      val rabbitPtY = trY - (prevRabbitY * trScale).toInt()
      g.drawLine(rabbitPtX, rabbitPtY, trX + (calc.rabbitX * trScale).toInt(), trY - (calc.rabbitY * trScale).toInt())
      if (putMarker) {
        g.drawOval(rabbitPtX - 2, rabbitPtY - 2, 4, 4)
        g.setColor(Color.GREEN.darker())
        g.drawString(Integer.toString(counter), rabbitPtX, rabbitPtY)
      }

      ++step
      ++markerCounter
    }

    if (isTerm) {
      g.setColor(Color.BLACK)
      g.drawOval(foxPtX - 2, foxPtY - 2, 4, 4)
      g.setColor(Color.ORANGE)
      g.drawString(Integer.toString(counter + 1), foxPtX, foxPtY)
      g.drawString(Integer.toString(counter + 1), foxPtX + 1, foxPtY + 1)
    }

    // save chasing path
    ImageIO.write(image, "png", targetFile)
  }
}

fun drawLinearChasingPath() {
  val calc = LinearChasingCalc()
  val drawer = ChasingPathDrawer()

  drawer.drawPath(calc, File(System.getProperty("user.home") + "/Downloads/1.png"))
}

fun drawCircChasingPath() {
  val calc = CircChasingCalc(maxSteps = 60000, foxVelocity = 0.1055, rabbitCenterX = 4.0, rabbitCircRadius = 4.0)
  val drawer = ChasingPathDrawer(trScale = 50, trY = 260, markerSentinel = 9000)

  drawer.drawPath(calc, File(System.getProperty("user.home") + "/Downloads/2.png"))
}

fun printChasingPath() {
  val chasing = LinearChasingCalc()

  var step = 0
  while (step < chasing.maxSteps) {
    if (!chasing.move()) {
      println("TERM at ${step}")
      break
    }

    println("Step ${step}: fox=(${chasing.foxX}, ${chasing.foxY}), rabbit=(${chasing.rabbitX}, ${chasing.rabbitY})")
    ++step
  }
}


fun main(args: Array<String>) {
  //drawLinearChasingPath()
  drawCircChasingPath()
}