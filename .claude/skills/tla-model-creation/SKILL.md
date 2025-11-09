---
name: tla-model-creation
description: Create and configure TLA+ model specifications for testing. Use when adding new models, modifying state machines, defining invariants, or creating test cases.
---

# TLA+ Model Creation

## Instructions

1. Create the TLA+ specification file (`.tla`)
2. Create the configuration file (`.cfg`)
3. Add to test references
4. Verify models are different from existing ones

## Basic Template

### ModelName.tla
```tla
---- MODULE ModelName ----
EXTENDS Naturals, Sequences

VARIABLE var1, var2

Init == var1 = init_value /\ var2 = init_value

Next == 
  /\ var1' = expression1
  /\ var2' = expression2

Inv == invariant_condition

====
```

### ModelName.cfg
```
INIT Init
NEXT Next
INVARIANT Inv
```

## Examples

**Example 1: Simple Counter (ModelCounter.tla)**
```tla
VARIABLE counter

Init == counter = 0

Next == counter' = IF counter < 5 THEN counter + 1 ELSE counter

Inv == counter <= 3
```

**Example 2: String Concatenation (ModelString.tla)**
```tla
EXTENDS Sequences

VARIABLE str

Init == str = ""

Next == 
  IF Len(str) < 2 THEN
    str' = str \o "x"
  ELSE
    UNCHANGED str

Inv == Len(str) <= 2
```

## Best practices

- Use completely different variables for each model
- Don't reuse the same model in test sequences
- Design invariants to either pass or fail clearly
- Keep models simple and understandable
- Use descriptive variable names
- Document your model's purpose

## Critical requirements

- Each model MUST be unique (different logic)
- Store in `test-model/` directory
- Create `.cfg` configuration file
- Reference from test code with full path
- Verify state space is reasonable size
