# JaVerT: JavaScript Verification Toolchain

JaVerT (pronounced [ʒavɛʁ]) is a toolchain for semi-automatic verification of functional correctness properties of JavaScript programs. It is based on separation logic and its structure is illustrated in the image below.

<img src="https://github.com/resource-reasoning/JaVerT/raw/master/images/JaVerT.png?raw=true" align="center" width="700">

The JaVerT pipeline works as follows. The user first annotates JavaScript code with pre- and post conditions for functions and top-level code, loop invariants, and tactics for the folding and unfolding of user-defined predicates. These annotations are written in JS Logic, a simple assertion language for JavaScript.

## Obtaining the Artifact

## Reproducing the Results

### Testing

### Verification 

The verification times have improved since the submission of the paper. The table below shows: 

1. The verification times stated in the paper (Intel Core i7-4980HQ CPU 2.80 GHz, DDR3 RAM 16GB, macOS Sierra 10.12.6); 
2. The current verification times (same configuration, accompanying screenshot below); and 
3. The verification times observed in the Virtual Machine (Intel Core i7-4980HQ CPU 2.80 GHz, 1 Core, DDR3 RAM 4GB, Ubuntu 17.04 Zesty Zapus).

| Example          | Paper (s)     | Current (s) | VM (s)  |
| ---------------- |:-------------:|:-----------:|:-------:|
| Key-value map    | 4.71          | 3.57        | 3.37    |
| ID Generator     | 1.87          | 0.79        | 0.73    |
| Priority queue   | 9.20          | 7.96        | 7.14    |
| BST              | 8.05          | 7.87        | 7.38    |
| Insertion sort   | 2.89          | 2.02        | 1.78    |
| Test262 examples | 9.01          | 3.69        | 3.46    |

<img src="https://github.com/resource-reasoning/JaVerT/raw/master/images/VerificationResults.png?raw=true" align="center" width="700">

**Note**: The Test262 examples comprise the switch-01, switch-02, try-catch-01, try-catch-02, and try-catch-03 examples.
