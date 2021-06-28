To build splat requires a recent installation of HOL. Its "Holmake"
tool is used to create the splat executable. In the splat directory
invoke

  Holmake splat

If this succeeds, the splat executable is created in the splat
directory. Following is an invocation of splat on JSON generated from
the Example_V4 model:


   $ ./splat examples/SW.json
   splat:
   Parsing /home/guardol/Projects/splat/examples/SW.json ... succeeded.
   Found 3 CASE security components.

   Processing "SW.Filter".
   Invocation dir: /home/guardol/Projects/splat
     Writing basis_ffi.c
     Writing Makefile
     Writing SW_Filter.cml
   Code written to directory: /home/guardol/Projects/splat/splat_outputs/SW_Filter
   Done.

   Processing "SW.Monitor".
   Invocation dir: /home/guardol/Projects/splat
     Writing basis_ffi.c
     Writing Makefile
     Writing SW_Monitor.cml
   Code written to directory: /home/guardol/Projects/splat/splat_outputs/SW_Monitor
   Done.

   Processing "SW.AttestationGate".
   Invocation dir: /home/guardol/Projects/splat
     Writing basis_ffi.c
     Writing Makefile
     Writing SW_AttestationGate.cml
   Code written to directory: /home/guardol/Projects/splat/splat_outputs/SW_AttestationGate
   Done.

Command Line Arguments.
------------------------

Invoking splat with no arguments results in the options being displayed:

   $ ./splat
   splat:
   Usage: splat [-target (hamr | standalone)]
                [-outdir <dirname>]
                [-intwidth <int>]
                [-endian (LSB | MSB)]
                <name>.json

The defaults are

   - build for HAMR API calls
   - directory where outputs are written is

        <invocation-dir>/splat_outputs

   - 32 bit integers
   - little-endian format
