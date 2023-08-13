# Bitwise Operations in Prolog

This repository contains a practice project aimed at reviewing fundamental concepts related to lists, structures, and recursion as studied in the subject "Declarative programming: logic and constraints". The goal of this practice is to implement a series of predicates that operate at the level of bits, nibbles, and bytes. Since pure Prolog lacks native support for such tasks, it becomes necessary to define types and operations for these functionalities.

## Implementation

To address the absence of native support for bit-level operations in Prolog, this project defines custom types and operations. For instance, a fundamental data type is introduced: the "bit." This is achieved through the structure ```bind/1```, representing a binary digit. Although numeric constants such as 1, 2, 5, etc., are used, it is crucial to understand that they signify constants rather than numeric expressions.

