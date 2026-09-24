/**************************************************************************
 *
 *      AI LANDSLIDE DETECTION SYSTEM
 *      Version 2.0
 *
 *      Edge Impulse
 *      Window : 10000 ms
 *      Frequency : 100 Hz
 *
 **************************************************************************/

#include <NAILS_inferencing.h>

#include <Wire.h>
#include "I2Cdev.h"
#include "MPU6050.h"

MPU6050 mpu;


//====================================================
// SENSOR PINS
//====================================================

#define SURFACE_SENSOR     33
#define DEEP_SENSOR        32


//====================================================
// OUTPUT PINS
//====================================================

#define YELLOW_LED         26
#define RED_LED            27
#define BUZZER             14


//====================================================
// EDGE IMPULSE SETTINGS
//====================================================

#define SAMPLE_INTERVAL_MS     10
#define EI_SAMPLE_COUNT        1000
#define AXES                   8

float features[EI_SAMPLE_COUNT * AXES];

int sampleIndex = 0;


//====================================================
// MPU6050 RAW DATA
//====================================================

int16_t ax;
int16_t ay;
int16_t az;

int16_t gx;
int16_t gy;
int16_t gz;


//====================================================
// SOIL VALUES
//====================================================

int surfaceValue = 0;
int deepValue = 0;


//====================================================
// TILT
//====================================================

float roll = 0.0;
float pitch = 0.0;
float tiltAngle = 0.0;


//====================================================
// AI PROBABILITIES
//====================================================

float normalProb = 0;
float warningProb = 0;
float dangerProb = 0;
float evacuateProb = 0;


//====================================================
// FINAL AI RESULT
//====================================================

String aiResult = "";

float aiConfidence = 0;

float riskScore = 0;


//====================================================
// RISK HISTORY
//====================================================

#define HISTORY_SIZE 5

float history[HISTORY_SIZE];

int historyIndex = 0;


//====================================================
// DANGER CONFIRMATION
//====================================================

#define DANGER_CONFIRMATION 3

int dangerCounter = 0;


//====================================================
// MANUAL OVERRIDE (trigger stages via Serial)
//====================================================
// When manualOverride is true, outputControl() drives the LEDs/
// buzzer from manualStage instead of the AI's aiResult. The AI
// keeps running in the background (so you can see what it *would*
// have decided in the 10s report), it just isn't allowed to touch
// the outputs until you send "AUTO".

bool   manualOverride = false;
String manualStage    = "NORMAL";


//====================================================
// TIMERS
//====================================================

unsigned long lastSampleTime = 0;


// NOTE:
// The old globals `signal_t signal;` and `ei_impulse_result_t prediction;`
// were removed from here. `signal` collided with the standard C library
// function signal() declared in signal.h (pulled in via ESP32 core headers),
// causing a "redeclared as different kind of entity" compile error.
// Neither global was actually used anywhere -- runAI() already declares
// its own local `signal` and `result` variables.


//====================================================
// MPU6050 OFFSETS
//====================================================

long axOffset = 0;
long ayOffset = 0;
long azOffset = 0;


//====================================================
// MELODIC ALARM PATTERNS
//====================================================
// Each melody is a set of parallel arrays: note frequency (Hz) and
// note duration (ms), plus a "gap" that's inserted before the melody
// repeats, and a VOLUME (0-100). Melodies get shorter/faster/louder
// as risk increases -- WARNING is the quietest, DANGER is the loudest.

// ---- WARNING melody: calm, gentle two-tone chime (QUIETEST) ----
const int warningNotes[]     = { 1568, 1976, 1568, 1976 };   // G6, B6, G6, B6
const int warningDurations[] = { 150,  150,  150,  150  };
const int WARNING_MELODY_LEN = 4;
const int WARNING_GAP_MS     = 900;   // long pause -> calm, unhurried
const int WARNING_VOLUME     = 100;    // quiet

// ---- POSSIBLE DANGER melody: quicker rising phrase (MEDIUM) ----
const int possibleDangerNotes[]     = { 1568, 1760, 1976, 2093 };  // G6 A6 B6 C7 (ascending)
const int possibleDangerDurations[] = { 110,  110,  110,  140  };
const int POSSIBLE_DANGER_MELODY_LEN = 4;
const int POSSIBLE_DANGER_GAP_MS     = 400;   // shorter pause -> more urgent
const int POSSIBLE_DANGER_VOLUME     = 200;    // medium

// ---- CONFIRMED DANGER melody: fast, jarring alternating siren-like run (LOUDEST) ----
const int dangerNotes[]     = { 2093, 1568, 2093, 1568, 2637, 1976 }; // C7 G6 C7 G6 E7 B6
const int dangerDurations[] = { 90,   90,   90,   90,   90,   120  };
const int DANGER_MELODY_LEN = 6;
const int DANGER_GAP_MS     = 120;    // near-continuous -> maximum urgency
const int DANGER_VOLUME     = 300;    // absolute max


//====================================================
// BUZZER VOLUME CONTROL (ESP32 LEDC PWM)
//====================================================
// tone()/noTone() on ESP32 always drive the buzzer at a fixed duty
// cycle -- frequency changes pitch, not loudness. To get real
// loudness control we drive the buzzer directly with LEDC and vary
// the PWM duty cycle, which controls how much power reaches the
// piezo each cycle (0% = silent, 50% = max loudness square wave).

#define BUZZER_RESOLUTION  8      // 8-bit duty range: 0-255
#define BUZZER_MAX_DUTY    128    // 50% duty = loudest a square wave gets

// NOTE: ESP32 Arduino core 3.x removed ledcSetup()/ledcAttachPin()/channel
// numbers. LEDC is now addressed directly by pin: ledcAttach(pin, freq, res)
// once in setup(), then ledcWriteTone(pin, freq) / ledcWrite(pin, duty).

void buzzerTone(int freq, int volumePercent)
{
    if (freq <= 0 || volumePercent <= 0)
    {
        ledcWrite(BUZZER, 0);
        return;
    }

    if (volumePercent > 100) volumePercent = 100;

    ledcWriteTone(BUZZER, freq);

    int duty = map(volumePercent, 0, 100, 0, BUZZER_MAX_DUTY);
    ledcWrite(BUZZER, duty);
}

void buzzerOff()
{
    ledcWrite(BUZZER, 0);
}


//====================================================
// MELODY PLAYER STATE (non-blocking)
//====================================================

const int*   activeMelodyNotes     = nullptr;
const int*   activeMelodyDurations = nullptr;
int          activeMelodyLength    = 0;
int          activeMelodyGap       = 0;
int          activeMelodyVolume    = 0;

int           melodyNoteIndex      = 0;
unsigned long melodyNoteStartTime  = 0;
bool          melodyInGap          = false;
bool          melodyPlaying        = false;


//====================================================
// START A MELODY (only restarts if it's a different melody
// than the one currently playing, so it doesn't stutter)
//====================================================

void startMelody(const int* notes, const int* durations, int length, int gapMs, int volumePercent)
{
    if (activeMelodyNotes == notes && melodyPlaying)
    {
        // Already playing this exact melody, let it continue.
        return;
    }

    activeMelodyNotes     = notes;
    activeMelodyDurations = durations;
    activeMelodyLength    = length;
    activeMelodyGap       = gapMs;
    activeMelodyVolume    = volumePercent;

    melodyNoteIndex     = 0;
    melodyInGap         = false;
    melodyPlaying       = true;
    melodyNoteStartTime = millis();

    buzzerTone(activeMelodyNotes[0], activeMelodyVolume);
}


//====================================================
// STOP MELODY
//====================================================

void stopMelody()
{
    if (melodyPlaying)
    {
        buzzerOff();
    }

    activeMelodyNotes = nullptr;
    melodyPlaying     = false;
    melodyInGap        = false;
    melodyNoteIndex    = 0;
}


//====================================================
// UPDATE MELODY (call this every loop() iteration)
//====================================================

void updateMelody()
{
    if (!melodyPlaying || activeMelodyNotes == nullptr)
    {
        return;
    }

    unsigned long elapsed = millis() - melodyNoteStartTime;

    if (!melodyInGap)
    {
        // Waiting for current note to finish
        if (elapsed >= (unsigned long)activeMelodyDurations[melodyNoteIndex])
        {
            melodyNoteIndex++;

            if (melodyNoteIndex >= activeMelodyLength)
            {
                // Finished the phrase -> enter gap before repeating
                melodyNoteIndex     = 0;
                melodyInGap         = true;
                melodyNoteStartTime = millis();
                buzzerOff();
            }
            else
            {
                melodyNoteStartTime = millis();
                buzzerTone(activeMelodyNotes[melodyNoteIndex], activeMelodyVolume);
            }
        }
    }
    else
    {
        // Waiting out the gap between repeats
        if (elapsed >= (unsigned long)activeMelodyGap)
        {
            melodyInGap         = false;
            melodyNoteStartTime = millis();
            buzzerTone(activeMelodyNotes[0], activeMelodyVolume);
        }
    }
}


//====================================================
// CALIBRATE MPU6050
//====================================================

void calibrateMPU()
{
    long axSum = 0;
    long aySum = 0;
    long azSum = 0;

    const int samples = 500;

    for (int i = 0; i < samples; i++)
    {
        mpu.getMotion6(
            &ax,
            &ay,
            &az,
            &gx,
            &gy,
            &gz
        );

        axSum += ax;
        aySum += ay;

        // subtract 1 g from Z axis
        azSum += (az - 16384);

        delay(5);
    }

    axOffset = axSum / samples;
    ayOffset = aySum / samples;
    azOffset = azSum / samples;
}


//====================================================
// SETUP
//====================================================

void setup()
{
    Serial.begin(115200);

    Wire.begin();

    mpu.initialize();

    mpu.setFullScaleAccelRange(MPU6050_ACCEL_FS_2);
    mpu.setFullScaleGyroRange(MPU6050_GYRO_FS_250);

    if (!mpu.testConnection())
    {
        Serial.println();
        Serial.println("ERROR : MPU6050 NOT FOUND");

        while (1);
    }

    pinMode(SURFACE_SENSOR, INPUT);
    pinMode(DEEP_SENSOR, INPUT);

    pinMode(YELLOW_LED, OUTPUT);
    pinMode(RED_LED, OUTPUT);

    digitalWrite(YELLOW_LED, LOW);
    digitalWrite(RED_LED, LOW);

    // Set up buzzer as an LEDC PWM pin so we can control volume
    // (duty cycle) as well as pitch (frequency).
    ledcAttach(BUZZER, 2000, BUZZER_RESOLUTION);
    buzzerOff();

    calibrateMPU();

    Serial.println("System Ready");
}


//====================================================
// COLLECT SENSOR DATA
//====================================================

void collectData()
{
    // Read MPU6050
    mpu.getMotion6(
        &ax,
        &ay,
        &az,
        &gx,
        &gy,
        &gz
    );

    // Apply offsets from calibration
    ax -= axOffset;
    ay -= ayOffset;
    az -= azOffset;

    // Read soil sensors
    surfaceValue = analogRead(SURFACE_SENSOR);
    deepValue = analogRead(DEEP_SENSOR);

    // Calculate roll and pitch (degrees)
    roll = atan2((float)ay, (float)az) * 180.0 / PI;

    pitch = atan2(
        -(float)ax,
        sqrt((float)ay * ay + (float)az * az)
    ) * 180.0 / PI;

    // Maximum tilt magnitude
    tiltAngle = max(abs(roll), abs(pitch));

    // Store sample for Edge Impulse
    if (sampleIndex < EI_SAMPLE_COUNT)
    {
        int base = sampleIndex * AXES;

        features[base + 0] = (float)ax;
        features[base + 1] = (float)ay;
        features[base + 2] = (float)az;

        features[base + 3] = (float)gx;
        features[base + 4] = (float)gy;
        features[base + 5] = (float)gz;

        features[base + 6] = (float)surfaceValue;
        features[base + 7] = (float)deepValue;

        sampleIndex++;
    }
}


//====================================================
// RUN EDGE IMPULSE AI
//====================================================

void runAI()
{
    signal_t signal;

    numpy::signal_from_buffer(
        features,
        EI_SAMPLE_COUNT * AXES,
        &signal
    );

    ei_impulse_result_t result;

    EI_IMPULSE_ERROR err =
        run_classifier(
            &signal,
            &result,
            false
        );

    if (err != EI_IMPULSE_OK)
    {
        Serial.println("Classifier failed!");
        sampleIndex = 0;
        return;
    }

    //------------------------------------------------
    // Reset probabilities
    //------------------------------------------------

    normalProb = 0;
    warningProb = 0;
    dangerProb = 0;

    //------------------------------------------------
    // Read probabilities
    //------------------------------------------------

    for (size_t i = 0; i < EI_CLASSIFIER_LABEL_COUNT; i++)
    {

        String label =
            result.classification[i].label;

        float value =
            result.classification[i].value;

        if(label == "NORMAL")
            normalProb = value;

        else if(label == "warning")
            warningProb = value;

        else if(label == "danger")
            dangerProb = value;

    }

    //------------------------------------------------
    // Find highest confidence
    //------------------------------------------------

    aiConfidence = max(
        normalProb,
        max(
            warningProb,
            dangerProb
        )
    );

    //------------------------------------------------
    // Weighted Risk Score
    //------------------------------------------------

    riskScore =
        warningProb * 50.0 +
        dangerProb * 100.0;

    //------------------------------------------------
    // Tilt adjustment
    //------------------------------------------------

    if(tiltAngle > 5)
        riskScore += 5;

    if(tiltAngle > 10)
        riskScore += 10;

    if(tiltAngle > 15)
        riskScore += 20;

    //------------------------------------------------
    // Soil adjustment
    //------------------------------------------------

    if(surfaceValue < 2600)
        riskScore += 5;

    if(surfaceValue < 2200)
        riskScore += 10;

    if(deepValue < 2600)
        riskScore += 5;

    if(deepValue < 2200)
        riskScore += 10;

    //------------------------------------------------
    // Limit score
    //------------------------------------------------

    if(riskScore > 100)
        riskScore = 100;

    //------------------------------------------------
    // Moving average
    //------------------------------------------------

    history[historyIndex] = riskScore;

    historyIndex++;

    if(historyIndex >= HISTORY_SIZE)
        historyIndex = 0;

    float averageRisk = 0;

    for(int i = 0; i < HISTORY_SIZE; i++)
    {
        averageRisk += history[i];
    }

    averageRisk /= HISTORY_SIZE;

    //------------------------------------------------
    // Final decision
    //------------------------------------------------

    if(averageRisk < 30)
    {
        aiResult = "NORMAL";
    }
    else if(averageRisk < 65)
    {
        aiResult = "warning";
    }
    else
    {
        aiResult = "danger";
    }

    sampleIndex = 0;
}


//====================================================
// SERIAL COMMANDS (manual stage trigger)
//====================================================
// Open the Serial Monitor (115200 baud), set line ending to
// "Newline", and type one of:
//
//   NORMAL    -> force NORMAL stage
//   WARNING   -> force WARNING stage
//   POSSIBLE  -> force DANGER stage, unconfirmed (yellow LED + medium alarm)
//   DANGER    -> force DANGER stage, confirmed   (red LED + loud alarm)
//   AUTO      -> hand control back to the AI
//   HELP      -> list commands
//
// Commands are case-insensitive.

void handleSerialCommands()
{
    if (!Serial.available())
        return;

    String cmd = Serial.readStringUntil('\n');
    cmd.trim();
    cmd.toUpperCase();

    if (cmd.length() == 0)
        return;

    if (cmd == "NORMAL")
    {
        manualOverride = true;
        manualStage    = "NORMAL";
        Serial.println(">> MANUAL: NORMAL");
    }
    else if (cmd == "WARNING")
    {
        manualOverride = true;
        manualStage    = "warning";
        Serial.println(">> MANUAL: WARNING");
    }
    else if (cmd == "POSSIBLE")
    {
        manualOverride = true;
        manualStage    = "danger";
        dangerCounter  = 0;   // below DANGER_CONFIRMATION -> "possible danger" branch
        Serial.println(">> MANUAL: DANGER (unconfirmed / possible)");
    }
    else if (cmd == "DANGER")
    {
        manualOverride = true;
        manualStage    = "danger";
        dangerCounter  = DANGER_CONFIRMATION;   // forces the confirmed-danger branch
        Serial.println(">> MANUAL: DANGER (confirmed)");
    }
    else if (cmd == "AUTO")
    {
        manualOverride = false;
        Serial.println(">> AUTO: AI back in control");
    }
    else if (cmd == "HELP" || cmd == "?")
    {
        Serial.println("Commands: NORMAL | WARNING | POSSIBLE | DANGER | AUTO | HELP");
    }
    else
    {
        Serial.print(">> Unknown command: ");
        Serial.println(cmd);
        Serial.println("Type HELP for options.");
    }
}


//====================================================
// OUTPUT CONTROL
//====================================================

void outputControl()
{
    // Manual override replaces the AI's result, but the confirmation
    // counter logic below is only run when the AI is actually deciding
    // (in manual mode, dangerCounter is set directly by the command).
    String effectiveResult = manualOverride ? manualStage : aiResult;

    //------------------------------------------------
    // NORMAL
    //------------------------------------------------

    if(effectiveResult == "NORMAL")
    {
        dangerCounter = 0;

        digitalWrite(YELLOW_LED, LOW);
        digitalWrite(RED_LED, LOW);

        stopMelody();

        return;
    }

    //------------------------------------------------
    // WARNING
    //------------------------------------------------

    if(effectiveResult == "warning")
    {
        dangerCounter = 0;

        digitalWrite(YELLOW_LED, HIGH);
        digitalWrite(RED_LED, LOW);

        startMelody(warningNotes, warningDurations, WARNING_MELODY_LEN, WARNING_GAP_MS, WARNING_VOLUME);

        return;
    }

    //------------------------------------------------
    // DANGER
    //------------------------------------------------

    if(effectiveResult == "danger")
    {
        if(!manualOverride)
        {
            if(aiConfidence >= 0.70)
            {
                dangerCounter++;
            }
            else
            {
                if(dangerCounter > 0)
                    dangerCounter--;
            }
        }

        //------------------------------------------------
        // Not enough confirmations
        //------------------------------------------------

        if(dangerCounter < DANGER_CONFIRMATION)
        {
            digitalWrite(YELLOW_LED, HIGH);
            digitalWrite(RED_LED, LOW);

            startMelody(possibleDangerNotes, possibleDangerDurations, POSSIBLE_DANGER_MELODY_LEN, POSSIBLE_DANGER_GAP_MS, POSSIBLE_DANGER_VOLUME);

            return;
        }

        //------------------------------------------------
        // Confirmed Danger
        //------------------------------------------------

        digitalWrite(YELLOW_LED, LOW);
        digitalWrite(RED_LED, HIGH);

        startMelody(dangerNotes, dangerDurations, DANGER_MELODY_LEN, DANGER_GAP_MS, DANGER_VOLUME);

        return;
    }

    //------------------------------------------------
    // Fallback
    //------------------------------------------------

    digitalWrite(YELLOW_LED, LOW);
    digitalWrite(RED_LED, LOW);

    stopMelody();
}


//====================================================
// RESET AI BUFFER
//====================================================

void resetBuffer()
{
    sampleIndex = 0;

    memset(features, 0, sizeof(features));
}


//====================================================
// DISPLAY RESULT + SENSOR READINGS
//====================================================

void displayStatus()
{
    Serial.println();
    Serial.println("========== 10s REPORT ==========");

    Serial.print("Mode         : ");
    Serial.println(manualOverride ? "MANUAL" : "AUTO");

    Serial.print("Result       : ");
    Serial.println(manualOverride ? manualStage : aiResult);

    if (manualOverride)
    {
        Serial.print("(AI would say: ");
        Serial.print(aiResult);
        Serial.println(") -- type AUTO to hand back control");
    }

    Serial.print("Confidence   : ");
    Serial.print(aiConfidence * 100, 1);
    Serial.println("%");

    Serial.print("Risk Score   : ");
    Serial.print(riskScore, 1);
    Serial.println("/100");

    Serial.print("Tilt Angle   : ");
    Serial.print(tiltAngle, 1);
    Serial.println(" deg");

    Serial.print("AX/AY/AZ     : ");
    Serial.print(ax);
    Serial.print(" / ");
    Serial.print(ay);
    Serial.print(" / ");
    Serial.println(az);

    Serial.print("GX/GY/GZ     : ");
    Serial.print(gx);
    Serial.print(" / ");
    Serial.print(gy);
    Serial.print(" / ");
    Serial.println(gz);

    Serial.print("Surface Soil : ");
    Serial.println(surfaceValue);

    Serial.print("Deep Soil    : ");
    Serial.println(deepValue);

    Serial.print("Danger Count : ");
    Serial.print(dangerCounter);
    Serial.print(" / ");
    Serial.println(DANGER_CONFIRMATION);

    Serial.println("=================================");
}


//====================================================
// MAIN LOOP
//====================================================

void loop()
{
    unsigned long now = millis();

    //------------------------------------------------
    // Check for manual stage-trigger commands from Serial
    //------------------------------------------------

    handleSerialCommands();

    //------------------------------------------------
    // Collect data exactly every 10 ms
    //------------------------------------------------

    if (now - lastSampleTime >= SAMPLE_INTERVAL_MS)
    {
        lastSampleTime = now;

        collectData();
    }

    //------------------------------------------------
    // Advance whichever melody is currently active.
    // Must run every loop iteration (not just once per
    // 10s AI window) so the notes play back in time
    // without blocking sensor sampling.
    //------------------------------------------------

    updateMelody();

    //------------------------------------------------
    // Drive LEDs/buzzer every loop iteration (not just
    // once per 10s AI window) so manual Serial commands
    // take effect immediately instead of waiting for the
    // next AI cycle.
    //------------------------------------------------

    outputControl();

    //------------------------------------------------
    // AI every 1000 samples (10 seconds)
    //------------------------------------------------

    if (sampleIndex >= EI_SAMPLE_COUNT)
    {
        runAI();

        displayStatus();

        resetBuffer();
    }
}
