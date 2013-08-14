package com.alexshabanov.dogchase;

/**
 * Entry point.
 */
public final class App {

    //private final double dogV = 1.617; - this won't work:)
    private final double dogV = 1.618;
    private final double rabbitV = 1.0;

    private double dogX = 1.0;
    private double dogY = 0.0;
    private double rabbitX = 0.0;
    private double rabbitY = 0.0;

    //
    // calculations
    //

    private final double termDistance = 0.001;

    private final long maxSteps = 1000L;

    private double time = 0;
    private final double timeStep = 0.001;

    //
    // move
    //

    private boolean move() {
        final double dx = rabbitX - dogX;
        final double dy = rabbitY - dogY;
        final double dist = Math.sqrt(dx * dx + dy * dy);
        if (dist <= termDistance) {
            // terminal point
            return false;
        }

        // take time into an account
        time += timeStep;

        // dog's step
        final double dogStep = timeStep * dogV;
        // calc dog's radial velocity's projections
        final double distRatio = dogStep / dist;
        dogX += dx * distRatio;
        dogY += dy * distRatio;

        // rabbit's step
        final double rabbitStep = timeStep * rabbitV;
        //  rabbitX won't change
        rabbitY += rabbitStep;

        System.out.println("dist=" + dist +
                "dogX=" + dogX + ", dogY=" + dogY + "; rabbitX=" + rabbitX + ", rabbitY=" + rabbitY);

        return true;
    }


    private void doMoves() {
        for (long step = 0; step < maxSteps; ++step) {
            if (!move()) {
                return;
            }
        }
    }

    public void run() {
        doMoves();

        final double dx = rabbitX - dogX;
        final double dy = rabbitY - dogY;
        final double dist = Math.sqrt(dx * dx + dy * dy);

        System.out.println("Distance " + (dist < termDistance ? "TERMINAL!!!" : "non-terminal"));
    }


    public static void main(String[] args) {
        System.out.println("Chase calc");
        new App().run();
    }
}
