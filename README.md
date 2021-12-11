# Verifiable Prescriptions in Rosette
## How to run the tool
To run the tool, run any of the Racket files below. `tests.rkt` gives an overview of each feature (i.e., verification, synthesis, optimization) as well as detailed commentary for guidance. Each file represents a scenario.
- `asthma.rkt` is the toy example from the presentation.
- `hypertension.rkt` encodes hypertension interactions from the case study.
- `tests.rkt` represents an average drug knowledge and tests most features of the DSL.
- `moredrugs.rkt` represents a large set of drugs for benchmarking.
- `moreconflicts.rkt` represents a large set of drugs and conflicts for benchmarking.

## Implementation files
In addition to the scenarios, there is three more files:
- `database.rkt` contains lists of drug names, side effects, and properties. This file was supposed to host the data generator.
- `prescriptions.rkt` contains the DSL, the encoding, and the implementation.
- `utils.rkt` contains various utilities.


## Authors
Dhruv Yadav, Thomas Schweizer, Dan Cascaval