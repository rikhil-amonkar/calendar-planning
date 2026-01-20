# Guide for Multi-Pass Run - For Ceyhun

## Overview

This guide explains the multi-pass (iterations) evaluation system that was created based on your original single-pass evaluation framework. The iterations system allows models to refine their solutions through multiple attempts, which should theoretically improve accuracy.

## Background Context

### Original Setup

In the original repository's `data/` folder, there are two key JSON files for meeting planning:

1. **`meeting_planning_100.json`** - Contains the actual problem examples with:
   - Zero-shot prompts
   - Five-shot prompts  
   - Golden solutions
   - Full problem specifications

2. **`meeting_planning_100_constraints.json`** - Contains constraints extracted from the problems (created with Harry), but uses a different structure than your constraints file.

### Your Original Framework

Your original framework (located in the `improved/` folder) includes:
- `code_generation_inference.py` - Single-pass inference
- `convert_to_structured_output.py` - Converts text outputs to structured JSON
- `evaluate_structured_outputs.py` - Evaluates against constraints
- `meeting_planning_100_constraints.json` - Your constraints file structure

## The Iterations System

### New Files Created

Three new iterations versions were created, each with `_iterations` suffix:

1. **`code_generation_inference_iterations.py`**
   - Runs inference with multiple iterations/retries
   - Allows models to refine their code solutions
   - Tracks each iteration attempt

2. **`convert_to_structured_output_iterations.py`**
   - Processes outputs from the iterations inference
   - Extracts structured data from the final successful iteration
   - Preserves iteration metadata

3. **`evaluate_structured_outputs_iterations.py`**
   - Evaluates the final iteration result (not just the first attempt)
   - Provides statistics about iteration success rates
   - Compares against constraints

### How Iterations Work

The iterations system works as follows:

1. **First Attempt**: Model generates code and executes it
2. **Check Success**: If execution fails or produces invalid output, the model gets feedback
3. **Retry**: Model can refine its solution based on errors
4. **Final Evaluation**: Only the final successful iteration (or last attempt) is evaluated

This should theoretically improve accuracy because models get multiple chances to fix errors.

## Constraints File Restructuring

### The Problem

Initially, the iterations system was evaluated against the original constraints file from `data/meeting_planning_100_constraints.json`, which had a different structure:
- Used `min_meeting_duration` field
- Included `prompt_0shot` and `golden_plan` fields
- Different field ordering

### The Solution

A new constraints file was created: **`meeting_planning_100_constraints_part_two.json`**

This file:
- Uses the same structure as your `meeting_planning_100_constraints.json`
- Contains the same 100 examples from the data folder
- Uses `min_duration` instead of `min_meeting_duration`
- Has clean structure: `{problem_id: {"constraints": {...}}}`
- Field order: `start`, `people_to_meet`, `travel_distances`

### Constraints File Structure

```json
{
  "meeting_planning_example_1": {
    "constraints": {
      "start": {
        "location": "Richmond District",
        "time_of_day": "9:00AM"
      },
      "people_to_meet": [
        {
          "name": "Betty",
          "location": "Financial District",
          "time_of_day": {
            "from": "5:15PM",
            "to": "9:45PM"
          },
          "min_duration": 60
        }
      ],
      "travel_distances": [
        {
          "place": {
            "from": "Richmond District",
            "to": "Financial District"
          },
          "walking_time": 22
        }
      ]
    }
  }
}
```

## Evaluation Scripts

### Part One (Original)

**`evaluate_structured_outputs_iterations.py`**
- Evaluates against original constraints structure
- Outputs to: `eval_results/{filename}_constraint_eval.json`

### Part Two (New Structure)

**`evaluate_structured_outputs_iterations_part_two.py`**
- Evaluates against new constraints structure (`meeting_planning_100_constraints_part_two.json`)
- Uses same evaluation logic as your `evaluate_structured_outputs.py`
- Outputs to: `eval_results/{filename}_structured_iterations_part_two_constraint_eval.json`
- Ensures proper field scraping and comparison

## Running the Multi-Pass System

### Step 1: Run Inference with Iterations

```bash
cd improved/
python code_generation_inference_iterations.py \
    --model gpt-5-2025-08-07 \
    --task_type meeting \
    --prompt_strategy prompt_strategy_python.txt \
    --dataset_file ../data/meeting_planning_100.json \
    --output_dir code_generation_results/
```

This will generate files in `code_generation_results/` with iteration data.

### Step 2: Convert to Structured Output

```bash
python convert_to_structured_output_iterations.py \
    code_generation_results/meeting_python_gpt-5-2025-08-07_YYYYMMDD_HHMMSS.json
```

This creates structured output in `structured_results/` folder.

### Step 3: Evaluate Against Constraints

**Using Part Two (Recommended):**
```bash
python evaluate_structured_outputs_iterations_part_two.py \
    structured_results/meeting_python_gpt-5-2025-08-07_YYYYMMDD_HHMMSS_structured_iterations.json \
    meeting_planning_100_constraints_part_two.json
```

**Using Part One (Original):**
```bash
python evaluate_structured_outputs_iterations.py \
    structured_results/meeting_python_gpt-5-2025-2025-08-07_YYYYMMDD_HHMMSS_structured_iterations.json \
    meeting_planning_100_constraints.json
```

## Results Location

### Code Generation Results
- Location: `code_generation_results/`
- Format: `meeting_{task_type}_{model}_{timestamp}.json`
- Contains: Raw model outputs, code, execution results, iteration data

### Structured Results
- Location: `structured_results/`
- Format: `{input_filename}_structured_iterations.json`
- Contains: Extracted itineraries, iteration metadata

### Evaluation Results
- Location: `eval_results/`
- Format: 
  - Part One: `{filename}_constraint_eval.json`
  - Part Two: `{filename}_structured_iterations_part_two_constraint_eval.json`
- Contains: Evaluation scores, violation details, iteration statistics

## Understanding the Results

### Evaluation Output Structure

```json
{
  "summary": {
    "total": 100,
    "with_plans": 95,
    "no_plans": 5,
    "correct": 55,
    "accuracy": 0.55,
    "iteration_stats": {
      "total_iterations": 150,
      "problems_with_iterations": 100,
      "problems_successful_on_first": 40,
      "problems_successful_after_retries": 15,
      "problems_failed_all_iterations": 45
    }
  },
  "results": [...]
}
```

### Key Metrics

- **accuracy**: Overall correctness rate (should be higher with iterations)
- **problems_successful_on_first**: How many got it right on first try
- **problems_successful_after_retries**: How many needed multiple attempts
- **problems_failed_all_iterations**: How many never succeeded

## Current Findings

### The Issue

When running evaluations:
- **Original constraints file**: ~55% accuracy
- **New constraints structure (part_two)**: Still ~55% accuracy

This suggests the constraints file structure is **not** the problem. The evaluation logic itself may need investigation.

### What Was Tested

- Used your prompt strategies (`prompt_strategy_python.txt` and `prompt_strategy_smt.txt`)
- Ran multiple models (GPT-5, DeepSeek variants, O3-mini)
- Both Python and SMT approaches
- Verified constraints file structure matches yours
- Ensured evaluation script uses same field scraping

## Files Reference

### Input Files
- `../data/meeting_planning_100.json` - Original problem examples
- `meeting_planning_100_constraints_part_two.json` - Restructured constraints

### Scripts
- `code_generation_inference_iterations.py` - Multi-pass inference
- `convert_to_structured_output_iterations.py` - Structure conversion
- `evaluate_structured_outputs_iterations_part_two.py` - Evaluation (new structure)

### Output Directories
- `code_generation_results/` - Raw inference outputs
- `structured_results/` - Structured JSON outputs
- `eval_results/` - Final evaluation results

## Potential Issues to Investigate

1. **Evaluation Logic**: The `evaluate_meeting()` function may have issues
2. **Field Extraction**: The structured output conversion might miss some meetings
3. **Constraints Matching**: Problem IDs might not match between files
4. **Time Parsing**: Time format conversion might have edge cases
5. **Travel Time Validation**: Travel time constraints might be too strict

## Next Steps

1. **Compare with Your Results**: Run your original single-pass evaluation on the same examples
2. **Check Problem IDs**: Verify problem IDs match between structured outputs and constraints
3. **Inspect Failures**: Look at specific examples that failed to understand why
4. **Test Evaluation Function**: Manually verify evaluation logic on known cases

## Questions for Ceyhun

1. Could you share your original 100 meeting examples (the questions with zero-shot prompts, not constraints)?
2. Could you try running the iterations files and see if you spot any issues?
3. What accuracy did you get with your single-pass evaluation on your examples?
4. Are there any differences in how you handle edge cases in evaluation?

## Contact

If you need to run this or have questions, the files are all in the `improved/` folder. The key files to look at are:
- `evaluate_structured_outputs_iterations_part_two.py` - The evaluation script
- `meeting_planning_100_constraints_part_two.json` - The constraints file
- Results in `eval_results/` folder with `_part_two_` in the filename

---

**Note**: This system should theoretically improve accuracy since models get multiple chances. The fact that it's not improving suggests there may be an issue with either the evaluation logic or the way iterations are being processed.
