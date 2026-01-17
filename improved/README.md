# Evaluation and Inference Scripts for Natural Plan Meeting Tasks

This folder contains all scripts, prompts, and documentation for LLM evaluation on meeting planning tasks.

## 📁 Contents

### 1. Inference Scripts
- `code_generation_inference.py` - Main inference script (OpenAI, Deepseek)
- `local_model_inference.py` - Local model inference (Qwen)
- `conversation_manager.py` - Conversation management utility
- `interactive_chat.py` - Interactive CLI for testing

### 2. Evaluation Scripts
- `llm_judge_evaluator.py` - LLM-as-a-Judge evaluation (GPT-5.2)
- `evaluate_structured_outputs.py` - Constraint-based evaluation
- `convert_to_structured_output.py` - Convert text outputs to structured JSON
- `extract_meeting_constraints.py` - Extract constraints from dataset
- `compare_all_evaluations.py` - Generate comparison reports
- `batch_evaluate_all.sh` - Batch evaluation automation

### 3. Prompting Strategies
- `LLM_JUDGE_PROMPT.txt` - Complete LLM judge evaluation prompt
- `PROMPTING_STRATEGIES.md` - Documentation of Python vs SMT prompting

### 4. Data Files
- `meeting_planning_100_constraints.json` - Ground truth constraints
- Sample evaluation results

### 5. Documentation
- `EVALUATION_COMPARISON_REPORT.txt` - Comprehensive results comparison
- `GPT5_EVALUATION_DISAGREEMENT_ANALYSIS.txt` - Deep dive into evaluator differences
- `DEEPSEEK_SETUP.md` - Deepseek API integration guide
- `LOCAL_MODEL_SETUP.md` - Local model setup guide

## 🚀 Quick Start

### Running Inference

**OpenAI/Deepseek models:**
```bash
python code_generation_inference.py \
  --model gpt-4o-mini \
  --task meeting \
  --num_samples 100 \
  --temperature 0.7
```

**Local models (Qwen):**
```bash
python local_model_inference.py \
  --model_name Qwen/Qwen3-32B \
  --task_type meeting \
  --num_problems 100
```

### Running Evaluations

**LLM Judge:**
```bash
python llm_judge_evaluator.py \
  code_generation_results/output.json \
  gpt-5.2
```

**Constraint-Based:**
```bash
# Convert to structured format
python convert_to_structured_output.py code_generation_results/output.json

# Evaluate
python evaluate_structured_outputs.py \
  code_generation_results/output_structured.json \
  meeting_planning_100_constraints.json
```

## 📊 Key Findings

- **Python prompting >> SMT prompting** for this task
- **GPT-5 achieves 95% constraint-based accuracy** (best overall)
- **LLM judge is stricter** but has ~6% false negative rate
- **Constraint-based evaluation is more reliable** for feasibility

See `EVALUATION_COMPARISON_REPORT.txt` for complete results.

## 📝 Notes

- Requires OpenAI API key in `.env` file
- Optional: Deepseek API key for Deepseek models
- Local models require GPU and HuggingFace setup

