# Usage Examples

This document provides practical examples of running inference and evaluation.

## Setup

1. **Install dependencies:**
```bash
pip install openai python-dotenv pandas
```

2. **Configure API keys:**
```bash
# Copy template and add your keys
cp env_template.txt .env
# Edit .env and add:
# OPENAI_API_KEY=sk-...
# DEEPSEEK_API_KEY=sk-... (optional)
```

---

## Running Inference

### Example 1: GPT-4o-mini (Python Strategy)

```bash
python code_generation_inference.py \
  --model gpt-4o-mini \
  --task meeting \
  --num_samples 100 \
  --temperature 0.7
```

**Output:** `code_generation_results/meeting_test_gpt-4o-mini_TIMESTAMP.json`

### Example 2: GPT-5 (Python Strategy)

```bash
python code_generation_inference.py \
  --model gpt-5 \
  --task meeting \
  --num_samples 100
  # Note: No temperature parameter (not supported by GPT-5)
```

### Example 3: O3-mini (Python Strategy)

```bash
python code_generation_inference.py \
  --model o3-mini \
  --task meeting \
  --num_samples 100
  # Note: No temperature parameter (not supported by O3)
```

### Example 4: Deepseek-Reasoner (Python Strategy)

```bash
python code_generation_inference.py \
  --model deepseek-reasoner \
  --task meeting \
  --num_samples 100
  # Note: No temperature parameter (not supported by deepseek-reasoner)
```

### Example 5: Deepseek-Chat (Python Strategy)

```bash
python code_generation_inference.py \
  --model deepseek-chat \
  --task meeting \
  --num_samples 100 \
  --temperature 0.7
```

### Example 6: Qwen3-32B Local (Python Strategy)

```bash
python local_model_inference.py \
  --model_name Qwen/Qwen3-32B \
  --task_type meeting \
  --num_problems 100 \
  --max_new_tokens 2048
```

---

## Running Evaluations

### LLM Judge Evaluation

**Step 1: Run LLM Judge**
```bash
python llm_judge_evaluator.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000.json \
  gpt-5.2
```

**Output:** `meeting_test_gpt-4o-mini_20250116_120000_gpt-5_2_judge_eval.json`

**What it checks:**
- Constraint satisfaction (time windows, travel times, durations)
- Optimality (did it meet maximum possible people?)
- Text accuracy (are stated times correct?)
- Format validity (no mixed time formats like "21:45PM")

---

### Constraint-Based Evaluation

**Step 1: Convert to structured format**
```bash
python convert_to_structured_output.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000.json
```

**Output:** `meeting_test_gpt-4o-mini_20250116_120000_structured.json`

**Step 2: Evaluate constraints**
```bash
python evaluate_structured_outputs.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000_structured.json \
  meeting_planning_100_constraints.json
```

**Output:** `meeting_test_gpt-4o-mini_20250116_120000_structured_constraint_eval.json`

**What it checks:**
- Time window constraints (meetings within availability)
- Travel time feasibility (enough time to travel between locations)
- Meeting durations (minimum duration requirements)
- Does NOT check: optimality, text accuracy

---

### Batch Evaluation (Multiple Files)

```bash
# Make script executable
chmod +x batch_evaluate_all.sh

# Run on all result files
./batch_evaluate_all.sh
```

This will:
1. Find all `meeting_test_*.json` files in `code_generation_results/`
2. Convert each to structured format
3. Run constraint-based evaluation
4. Generate summary reports

---

### Comparison Report

**Generate comprehensive comparison:**
```bash
python compare_all_evaluations.py
```

**Output:** `EVALUATION_COMPARISON_REPORT.txt`

This compares:
- LLM judge accuracy vs Constraint-based accuracy
- Python strategy vs SMT strategy
- All models side-by-side

---

## Complete Workflow Example

Here's a complete workflow from inference to comparison:

```bash
# 1. Run inference with GPT-4o-mini
python code_generation_inference.py \
  --model gpt-4o-mini \
  --task meeting \
  --num_samples 100 \
  --temperature 0.7

# Output: code_generation_results/meeting_test_gpt-4o-mini_20250116_120000.json

# 2. Run LLM judge evaluation
python llm_judge_evaluator.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000.json \
  gpt-5.2

# Output: meeting_test_gpt-4o-mini_20250116_120000_gpt-5_2_judge_eval.json

# 3. Convert to structured format
python convert_to_structured_output.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000.json

# Output: meeting_test_gpt-4o-mini_20250116_120000_structured.json

# 4. Run constraint-based evaluation
python evaluate_structured_outputs.py \
  code_generation_results/meeting_test_gpt-4o-mini_20250116_120000_structured.json \
  meeting_planning_100_constraints.json

# Output: meeting_test_gpt-4o-mini_20250116_120000_structured_constraint_eval.json

# 5. Generate comparison report (after running multiple models)
python compare_all_evaluations.py

# Output: EVALUATION_COMPARISON_REPORT.txt
```

---

## Understanding Output Files

### Inference Output (`*.json`)
```json
{
  "problem_id": "meeting_planning_example_1",
  "problem": "You need to meet...",
  "output": ["You start at...", "You travel to..."],
  "golden_solution": ["Reference solution..."],
  "execution_time": 2.5
}
```

### LLM Judge Output (`*_judge_eval.json`)
```json
{
  "problem_id": "meeting_planning_example_1",
  "judge_verdict": "CORRECT",
  "judge_reasoning": "The solution satisfies all constraints...",
  "judge_issues": "none",
  "problem": "...",
  "output": "...",
  "golden_solution": "..."
}
```

### Constraint Evaluation Output (`*_constraint_eval.json`)
```json
{
  "results": [
    {
      "problem_id": "meeting_planning_example_1",
      "is_correct": true,
      "status": "correct",
      "num_meetings": 5,
      "violated_constraint": {}
    }
  ],
  "summary": {
    "total": 100,
    "correct": 95,
    "accuracy": 0.95
  }
}
```

---

## Tips and Tricks

### 1. Testing on Small Samples First
```bash
# Test with just 5 problems
python code_generation_inference.py \
  --model gpt-4o-mini \
  --task meeting \
  --num_samples 5 \
  --temperature 0.7
```

### 2. Debugging Failed Evaluations
```python
# Look at specific problem
import json
with open('code_generation_results/meeting_test_gpt-4o-mini_20250116_120000_gpt-5_2_judge_eval.json') as f:
    data = json.load(f)
    incorrect = [d for d in data if d['judge_verdict'] == 'INCORRECT']
    print(f"Found {len(incorrect)} incorrect solutions")
    print(incorrect[0])  # Show first incorrect case
```

### 3. Comparing Two Models
```bash
# Run both models
python code_generation_inference.py --model gpt-4o-mini --task meeting --num_samples 100
python code_generation_inference.py --model gpt-5 --task meeting --num_samples 100

# Evaluate both
python llm_judge_evaluator.py code_generation_results/meeting_test_gpt-4o-mini_*.json gpt-5.2
python llm_judge_evaluator.py code_generation_results/meeting_test_gpt-5_*.json gpt-5.2

# Generate comparison
python compare_all_evaluations.py
```

---

## Troubleshooting

### Issue: "API key not found"
**Solution:** Make sure `.env` file exists with `OPENAI_API_KEY=sk-...`

### Issue: "Temperature not supported"
**Solution:** Don't use `--temperature` with o1, o3, gpt-5, or deepseek-reasoner models

### Issue: "CUDA out of memory" (local models)
**Solution:** Reduce batch size or use smaller model

### Issue: "No module named 'openai'"
**Solution:** Activate virtual environment: `source /path/to/venv/bin/activate`