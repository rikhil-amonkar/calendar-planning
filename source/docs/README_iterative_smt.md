# Iterative SMT Refinement with Constraint Feedback

This script implements an iterative refinement process for solving scheduling problems using Z3 SMT solver with LLM-generated code.

## Overview

The script combines the functionality of three existing components:
1. **Code Generation** (like `generate_smt_input.py`): Generates Z3 solution code using LLMs
2. **Code Execution** (like `execute_smt.py`): Executes the generated Python/Z3 code
3. **Constraint Evaluation** (like `evaluate_by_constraint.py`): Evaluates solutions against domain constraints

## Key Features

- **Iterative Refinement**: If a solution fails (execution errors or constraint violations), the script provides feedback and asks the LLM to fix the code
- **Multi-Pass Processing**: Each example can go through multiple refinement passes (default: 5)
- **Comprehensive Logging**: Saves conversation history, generated code, execution output, and evaluation results for each pass
- **Multiple Model Support**: Works with OpenAI models (GPT-4o-mini, O3-mini), DeepSeek models, and HuggingFace models
- **Smart Skip Logic**: Avoids re-processing examples that already have successful solutions

## Directory Structure

For each example, the script creates the following structure:
```
../output/SMT/{model_name}/{task}/n_pass/{example_id}/
├── 1_pass/
│   ├── conversation.json    # Full conversation history
│   ├── solution.py         # Generated Z3 code
│   ├── output.out          # Execution output
│   └── evaluation.json     # Constraint evaluation results
├── 2_pass/
│   └── ... (same structure)
└── ...
```

## Usage Examples

### Basic Usage
```bash
# Run calendar scheduling with GPT-4o-mini on examples 0-4
python iterative_smt_refinement.py --task calendar --model gpt-4o-mini --start 0 --end 5

# Run all tasks with multiple models
python iterative_smt_refinement.py --task all --model DeepSeek-V3 gpt-4o-mini

# Force re-run all examples (ignore existing results)
python iterative_smt_refinement.py --task meeting --model o3-mini --fresh
```

### Advanced Usage
```bash
# Limit to 3 refinement passes per example
python iterative_smt_refinement.py --task trip --model gpt-4o-mini --max_passes 3

# Process a specific range of examples
python iterative_smt_refinement.py --task calendar --model DeepSeek-V3 --start 10 --end 20
```

## Command Line Arguments

- `--task`: Task to run (`calendar`, `trip`, `meeting`, or `all`)
- `--model`: Model(s) to use (supports multiple models)
- `--fresh`: Re-run all examples, ignoring existing successful solutions
- `--start`: Starting index for processing examples (default: 0)
- `--end`: Ending index for processing examples (default: -1, process all)
- `--max_passes`: Maximum number of refinement passes per example (default: 5)

## Prerequisites

1. **API Keys**: Create `../../scheduling_key.json` with your API keys:
```json
{
    "openai": "your_openai_api_key",
    "deepseek": "your_deepseek_api_key"
}
```

2. **Dependencies**: Install required packages:
```bash
pip install kani openai asyncio
```

3. **Data Files**: Ensure these files exist in `../data/`:
   - `calendar_scheduling_100.json` and `calendar_scheduling_100_constraints.json`
   - `trip_planning_100.json` and `trip_planning_100_constraints.json`
   - `meeting_planning_100.json` and `meeting_planning_100_constraints.json`

## How It Works

### 1. Initial Code Generation
- Loads the problem description from the data file
- Sends a prompt to the LLM asking for Z3 code to solve the problem
- Extracts Python code from the LLM response

### 2. Code Execution
- Runs the generated Python code with a 10-second timeout
- Captures stdout and stderr output

### 3. Error Handling
- If execution fails: Provides error message to LLM for fixing
- If execution succeeds: Proceeds to constraint evaluation

### 4. Constraint Evaluation
- Parses the execution output to extract structured results using GPT-4.1-nano
- Evaluates against domain-specific constraints (time conflicts, travel constraints, etc.)
- If constraints are violated: Provides detailed feedback to LLM

### 5. Iterative Refinement
- Continues refinement passes until constraints are satisfied or max passes reached
- Each pass builds on the previous conversation history

## Constraint Types

### Calendar Scheduling
- Meeting duration must match requirements
- No conflicts with unavailable time slots
- Must specify day, start time, and end time

### Trip Planning
- Must cover exact number of days
- Respect minimum stay requirements in each city
- Must have direct flights between consecutive cities
- Handle city-specific events within visit windows

### Meeting Planning
- Must meet required number of people
- Respect individual availability windows
- Allow sufficient travel time between locations
- Handle starting location and time constraints

## Output Files

### conversation.json
Contains the full conversation history with the LLM, including prompts and responses for each pass.

### solution.py
The generated Python/Z3 code for the current pass.

### output.out
The execution output (stdout + stderr) from running the solution code.

### evaluation.json
Detailed evaluation results including:
- `has_execution_error`: Boolean indicating if code execution failed
- `constraints_satisfied`: Boolean indicating if all constraints are met
- `violated_constraints`: Details of any constraint violations
- `pred_formatted`: Structured output parsed from execution
- `pass_number`: Which refinement pass this represents

## Troubleshooting

### Common Issues

1. **Missing API Keys**: Ensure `../../scheduling_key.json` exists with valid keys
2. **Import Errors**: Install required dependencies (`pip install kani openai`)
3. **Timeout Errors**: Code execution is limited to 10 seconds
4. **File Not Found**: Ensure data files exist in the correct location

### Debug Tips

- Check conversation.json files to see the full interaction with the LLM
- Review evaluation.json files to understand why constraints were violated
- Examine solution.py files to see the generated code
- Use `--start` and `--end` to process smaller batches for testing 