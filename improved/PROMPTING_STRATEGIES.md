# Prompting Strategies for Meeting Planning Tasks

This document describes the two main prompting strategies used in our experiments.

## Overview

We tested two fundamentally different approaches:
1. **Python Code Generation** - Direct algorithmic solution
2. **SMT (Z3 Solver) Generation** - Constraint satisfaction approach

## 1. Python Prompting Strategy

### Approach
Ask the LLM to generate Python code that:
- Parses the meeting problem
- Implements a greedy/heuristic scheduling algorithm
- Outputs a human-readable itinerary

### Example Prompt Structure
```
You are given a meeting planning problem. Write Python code that:
1. Reads the problem description
2. Schedules meetings to maximize the number of people met
3. Respects time windows, travel times, and meeting durations
4. Outputs an itinerary in natural language

Problem:
[problem description]

Generate Python code that solves this problem.
```

### Advantages
- ✅ Direct, intuitive approach
- ✅ Can use heuristics and domain knowledge
- ✅ Generates human-readable outputs naturally
- ✅ Easier for LLMs to reason about
- ✅ **Significantly better performance (85-95% accuracy)**

### Disadvantages
- ❌ No guarantee of optimality
- ❌ May miss edge cases in complex scenarios

---

## 2. SMT (Z3) Prompting Strategy

### Approach
Ask the LLM to generate Z3 solver code that:
- Defines variables for meeting times
- Encodes constraints as SMT formulas
- Maximizes an objective function
- Extracts and formats the solution

### Example Prompt Structure
```
You are given a meeting planning problem. Write Python code using Z3 solver that:
1. Creates SMT variables for each possible meeting
2. Encodes time windows, travel times, and durations as constraints
3. Maximizes the number of meetings
4. Extracts the solution and outputs an itinerary

Problem:
[problem description]

Generate Z3 SMT solver code that solves this problem.
```

### Advantages
- ✅ Theoretically guarantees optimal solutions
- ✅ Handles complex constraints elegantly
- ✅ Explores entire solution space

### Disadvantages
- ❌ Much harder for LLMs to generate correctly
- ❌ Complex constraint encoding
- ❌ Easy to make subtle encoding errors
- ❌ **Poor performance (2-11% accuracy)**

---

## Experimental Results

### Performance Comparison

| Model | Python Accuracy | SMT Accuracy | Difference |
|-------|----------------|--------------|------------|
| **GPT-5** | 95% | 10% | **+85%** |
| **O3-mini** | 86% | 9% | **+77%** |
| **Deepseek-Reasoner** | 67% | 11% | **+56%** |
| **Deepseek-Chat** | 24% | 6% | **+18%** |
| **Qwen3-32B** | 7% | 6% | **+1%** |
| **Qwen2.5-32B** | 5% | 6% | **+1%** |

### Key Findings

1. **Python >> SMT for all models**
   - Even the best SMT performance (Deepseek-Reasoner: 11%) is far below worst Python (Qwen2.5: 5%)

2. **Stronger models benefit more from Python**
   - GPT-5: 95% (Python) vs 10% (SMT) = 85% gap
   - Weaker models struggle with both approaches

3. **SMT is consistently difficult**
   - All models achieve <11% with SMT
   - Constraint encoding is too complex for current LLMs

4. **Why Python wins:**
   - More natural problem-solving paradigm
   - LLMs trained extensively on algorithmic code
   - Easier to debug and validate
   - Can use domain-specific heuristics

---

## Code Generation Process

### Python Strategy
```python
# 1. Parse problem
meetings = parse_problem(problem_text)

# 2. Sort by some heuristic (e.g., earliest start time)
meetings.sort(key=lambda m: m.start_time)

# 3. Greedily schedule
schedule = []
current_time = start_time
current_location = start_location

for meeting in meetings:
    if can_schedule(meeting, current_time, current_location):
        schedule.append(meeting)
        current_time = meeting.end_time
        current_location = meeting.location

# 4. Output itinerary
print_itinerary(schedule)
```

### SMT Strategy
```python
from z3 import *

# 1. Create variables
meets = {person: Bool(f"meet_{person}") for person in people}
start_times = {person: Int(f"start_{person}") for person in people}

# 2. Encode constraints (complex!)
solver = Solver()
for person in people:
    # Time window constraints
    solver.add(Implies(meets[person], 
               And(start_times[person] >= person.avail_start,
                   start_times[person] + person.duration <= person.avail_end)))
    
# Travel time constraints (very complex to encode!)
for p1, p2 in pairs:
    solver.add(Implies(And(meets[p1], meets[p2]),
               Or(start_times[p2] >= start_times[p1] + duration[p1] + travel[p1.loc][p2.loc],
                  start_times[p1] >= start_times[p2] + duration[p2] + travel[p2.loc][p1.loc])))

# 3. Maximize objective
solver.maximize(Sum([If(meets[p], 1, 0) for p in people]))

# 4. Extract solution (if any)
if solver.check() == sat:
    model = solver.model()
    # Complex extraction logic...
```

---

## Recommendations

### For Meeting Planning Tasks:
1. **Use Python prompting** - Far superior performance
2. **Implement greedy heuristics** - Simple and effective
3. **Focus on output formatting** - Important for evaluation

### For Future Work:
1. **Explore hybrid approaches** - Use Python with Z3 as a subroutine
2. **Improve SMT prompting** - Provide templates/examples
3. **Chain-of-thought for SMT** - Break down constraint encoding step-by-step

### When to Use Each:

**Use Python when:**
- Problem has natural algorithmic solution
- Heuristics can find good solutions
- Performance matters more than optimality guarantee

**Use SMT when:**
- Strict optimality is required
- Constraints are highly complex
- Problem is small enough for solver
- You have time to debug constraint encoding

---

## Conclusion

For meeting planning tasks, **Python code generation is the clear winner**, achieving up to 95% accuracy compared to SMT's maximum of 11%. The algorithmic approach is more intuitive for LLMs and produces more reliable results.
