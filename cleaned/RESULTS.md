# Spurious Reasoning Filtering Summary

## Overview

This folder contains examples of **spurious reasoning** that were identified and filtered from model outputs. The original dataset consisted of 100 examples for each task type (calendar, meeting, trip, and zebralogic). Each model and method combination was evaluated on these 100 examples, and examples exhibiting spurious reasoning were identified and saved to this folder.

## Total JSON Files by Task Type

Across all models and methods, the total number of spurious reasoning examples found per task type:

- **Calendar**: 31
- **Meeting**: 117
- **Trip**: 300
- **ZebraLogic**: 53

## Breakdown by Method and Model

### Python Method

| Model | Calendar | Meeting | Trip | ZebraLogic |
|-------|----------|---------|------|------------|
| DeepSeek-R1 | 2/100 (2.0%) | 6/100 (6.0%) | 72/100 (72.0%) | 20/100 (20.0%) |
| DeepSeek-V3 | 0/100 (0.0%) | 11/100 (11.0%) | 54/100 (54.0%) | 1/100 (1.0%) |
| Qwen2.5-Coder-32B-Instruct | 1/100 (1.0%) | 3/100 (3.0%) | 6/100 (6.0%) | 4/100 (4.0%) |
| Qwen3-32B | 8/100 (8.0%) | 14/100 (14.0%) | 66/100 (66.0%) | 19/100 (19.0%) |

### SMT Method

| Model | Calendar | Meeting | Trip | ZebraLogic |
|-------|----------|---------|------|------------|
| DeepSeek-R1 | 0/100 (0.0%) | 1/100 (1.0%) | 13/100 (13.0%) | 0/100 (0.0%) |
| DeepSeek-V3 | 0/100 (0.0%) | 2/100 (2.0%) | 2/100 (2.0%) | 1/100 (1.0%) |
| Qwen2.5-Coder-32B-Instruct | 1/100 (1.0%) | 13/100 (13.0%) | 0/100 (0.0%) | 5/100 (5.0%) |
| Qwen3-32B | 19/100 (19.0%) | 67/100 (67.0%) | 87/100 (87.0%) | 3/100 (3.0%) |

## What is Spurious Reasoning?

Based on the classification script (`classify_spurious_reasoning.py`), **spurious reasoning** refers to a specific pattern where a model's reasoning content and code output function as two independent solution methods to the same problem.

### Definition

Spurious reasoning occurs when:
1. The model fully or near-fully solves the task in natural language (in the reasoning trace)
2. The reasoning does not rely on or build toward the code solution
3. The code follows a different or unrelated solution path compared to the reasoning
4. The reasoning and code function as two independent solution methods

**Key criterion**: The reasoning could be deleted entirely with no impact on the code's logic or construction.

### Classification Criteria

Examples are classified as spurious **only if**:
- The reasoning and code are independent solution methods
- The reasoning does not meaningfully correspond to the code (even loosely, implicitly, or only at the end)
- If uncertain, the classification defaults to "normal"

Examples are classified as normal if:
- The code meaningfully corresponds to the reasoning (even loosely, implicitly, or only at the end)
- There is any meaningful connection between the reasoning trace and the code output

## Experiment Background

### Purpose

This experiment was designed to identify and filter cases where language models exhibit a disconnect between their reasoning process and their code implementation. This is particularly relevant for models that use chain-of-thought reasoning or similar techniques where natural language reasoning precedes code generation.

### Methodology

1. **Data Collection**: The original dataset contained 100 examples for each of four task types:
   - Calendar scheduling
   - Meeting planning
   - Trip planning
   - ZebraLogic puzzles

2. **Model Evaluation**: Multiple models were tested using two different methods:
   - **Python**: Direct Python code generation
   - **SMT**: Satisfiability Modulo Theories (SMT) solver-based approaches

3. **Classification Process**: Using OpenAI's GPT-4o model, each example's reasoning content and code output were analyzed to determine if they represented independent solution paths.

4. **Filtration**: Only examples classified as "spurious" were saved to this folder. The classification was performed using a strict audit process that examined:
   - The original user prompt
   - The reasoning content (natural language reasoning trace)
   - The code content (implemented solution)

### What Filtration Meant

The filtration process served several purposes:

1. **Quality Assessment**: Identifying cases where models' reasoning processes don't align with their implementations, which may indicate:
   - Inefficient or redundant processing
   - Potential for improvement in model architectures
   - Training data or prompt engineering issues

2. **Dataset Curation**: Creating a clean dataset of problematic examples for further analysis, model improvement, or training data refinement.

3. **Pattern Recognition**: Understanding which tasks, models, or methods are more prone to producing spurious reasoning, which can inform future model development and evaluation strategies.

### Observations

From the data, we can observe:
- **Trip planning** tasks showed the highest incidence of spurious reasoning across models
- **Qwen3-32B with SMT method** showed particularly high rates of spurious reasoning (especially in meeting and trip tasks)
- **Calendar scheduling** generally showed lower rates of spurious reasoning
- **Python method** often showed higher rates than SMT method for some model/task combinations

These patterns suggest that certain task types or model/method combinations may be more prone to producing disconnected reasoning and implementation paths.
