//monitorBoundaries.h
#ifndef MONITOR_BOUNDARIES
#define MONITOR_BOUNDARIES

// cSpell:ignore debugf vcalc
//Turns on/off debug output
#define DEBUGF 0

#define EARTH_RADIUS_NM 3443.918
#define DEG2RAD (M_PI / 180.0)
#define RAD2DEG (180.0 / M_PI)
#define NM_PER_SEC_TO_KTS pow(60.0, 2.0)
#define NM_TO_FT 1852.0 * (1.0 / 0.3048)
#define VCALC_HORZ_BOUNDARY_THRESHOLD 25.0
#define VCALC_VERT_BOUNDARY_THRESHOLD 1600.0
#define USE_COMPLEX_BETA_CALC_THRESHOLD 0 // Set to 1 to use complex calc in calculateBetaCalcLowBound
#define BETA_CALC_BOUNDARY_THRESHOLD 12.0 // Otherwise use this value.
#define ORIENTATION_REF_ERROR 31.0
#define HALF_G_TAN_ROLL_ANGLE 1597.0
#define BETA_CALC_DENOM_COEFF 0.246202

#define DIV_BY_ZERO_THRESHOLD 0.0000000000000000001
//                              1234567890123456789
#define DIVIDE_BY_0_INDICATOR 0.0
#define BETA_CALC_MIN_BOUND_DEFAULT 0.0    //Also used when the calculation causes DIV-BY-ZERO
#define BETA_CALC_MAX_BOUND_DEFAULT 359.9999999  //Also used when the calculation causes DIV-BY-ZERO
#define VCALC_HORZ_MIN_BOUND_DEFAULT 0.0
#define VCALC_HORZ_MAX_BOUND_DEFAULT 5000.0
#define VCALC_VERT_MIN_BOUND_DEFAULT -132000.0
#define VCALC_VERT_MAX_BOUND_DEFAULT 132000.0

#define USE_SIMPLE_VCALC_VERT 1

#define INVALID_HEIGHT 101375.0
#define INVALID_VERTICAL_VEL -131072.0 ////TODO int or double?
#define INVALID_HORZ_SPEED 4095

/* note:
    phi = latitude
    lambda = longitude
    h = height
*/

/* --- types & structs --- */

typedef struct Boundary_s
{
    double vCalcHorzLowBound;
    double vCalcHorzHighBound;
    double betaCalcLowBound;
    double betaCalcHighBound;
    double vCalcVertLowBound;
    double vCalcVertHighBound;
} Boundary_s;

/* *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** 
 * REFERENCE THE .C FILE FOR FUNCTION COMMENTS AND USAGE   *** ***
 * *** *** *** *** *** *** *** *** *** *** *** *** *** *** *** ***/

// ********** --- struct "methods" **************
void printBoundaryRecord(struct Boundary_s b);

// ********** helper/debug functions ************
void debugf(const char* format, ...);

// ********** intermediate functions ************

double degreesToRadians(double degrees);

double calculateDCalcNmPerSec(double latRad1, double latRad2, double lonRad1, double lonRad2);
double calculateVCalcHorzFromDCalc(double dCalc_NmPerSec);
bool checkBetaCalcForDivideByZero(double lat1, double lat2, double lon1, double lon2);
double calculatebetaCalc(double lat1, double lat2, double lon1, double lon2);


// ********** boundary functions ****************

double calculateVCalcHorzLowBound(double vCalcHorz);
double calculateVCalcHorzHighBound(double vCalcHorz);

double calculateBetaCalcLowBound(double betaCalc, double dCalc);
double calculateBetaCalcHighBound(double betaCalc, double dCalc);

double calculateVCalcVertLowBound(double height1, double height2);
double calculateVCalcVertHighBound(double height1, double height2);

// ******** One interface to rule them all *******
Boundary_s calculateBoundaries(double lat1, double lat2,
                               double lon1, double lon2,
                               double height1, double height2, double horz_speed,
                               double nic1, double nic2, double trackType, double vertVelocity);

#endif