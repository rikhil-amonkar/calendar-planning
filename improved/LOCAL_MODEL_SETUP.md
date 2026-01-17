# Local Model Inference Setup

This guide explains how to run inference with local Qwen models (Qwen-2.5-32B-Instruct and Qwen-3-32B).

## Overview

The `local_model_inference.py` script allows you to run code generation inference using locally hosted Qwen models from HuggingFace, stored in your local cache directory.

### Supported Models

1. **Qwen/Qwen2.5-32B-Instruct** - Already installed ✓
2. **Qwen/Qwen3-32B** - Needs installation

## Installation

### 1. Install Qwen-3-32B

Run this command to download and cache Qwen-3-32B to your local directory:

```bash
python3 << 'EOF'
from transformers import AutoTokenizer, AutoModelForCausalLM
import torch

model_name = "Qwen/Qwen3-32B"
cache_dir = "/local-ssd/cek99/hf/transformers/"

print(f"Downloading {model_name} to {cache_dir}")
print("This may take a while (model is ~64GB)...")

tokenizer = AutoTokenizer.from_pretrained(
    model_name,
    cache_dir=cache_dir,
    trust_remote_code=True
)

model = AutoModelForCausalLM.from_pretrained(
    model_name,
    cache_dir=cache_dir,
    torch_dtype=torch.bfloat16,
    device_map="auto",
    trust_remote_code=True
)

print(f"✓ Model downloaded successfully to {cache_dir}")
EOF
```

### 2. Verify Installation

Check that both models are in the cache directory:

```bash
ls -la /local-ssd/cek99/hf/transformers/ | grep Qwen
```

You should see:
- `models--Qwen--Qwen2.5-32B-Instruct` ✓
- `models--Qwen--Qwen3-32B` (after installation)

## Requirements

Make sure you have the required packages:

```bash
source /home/cek99/venv/bin/activate
pip install transformers torch accelerate bitsandbytes
```

## Usage

### Basic Command Structure

```bash
python local_model_inference.py <model_name> <strategy_file> <task_type> [num_problems]
```

**Arguments:**
- `model_name`: HuggingFace model identifier
  - `Qwen/Qwen2.5-32B-Instruct`
  - `Qwen/Qwen3-32B`
- `strategy_file`: Path to prompting strategy (e.g., `strategies/my_strategy3.txt`)
- `task_type`: `meeting`, `calendar`, or `trip`
- `num_problems`: Number of problems to run (default: 100)

### Example Commands

**Qwen-2.5-32B-Instruct on 100 meeting problems:**
```bash
cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate
python local_model_inference.py Qwen/Qwen2.5-32B-Instruct strategies/my_strategy3.txt meeting 100
```

**Qwen-3-32B on 100 meeting problems:**
```bash
cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate
python local_model_inference.py Qwen/Qwen3-32B strategies/my_strategy3.txt meeting 100
```

**Quick test with 5 problems:**
```bash
cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate
python local_model_inference.py Qwen/Qwen2.5-32B-Instruct strategies/my_strategy3.txt meeting 5
```

**Calendar planning:**
```bash
python local_model_inference.py Qwen/Qwen2.5-32B-Instruct strategies/my_strategy3.txt calendar 100
```

**Trip planning:**
```bash
python local_model_inference.py Qwen/Qwen2.5-32B-Instruct strategies/my_strategy3.txt trip 100
```

## Output

Results are saved to `code_generation_results/` directory:

```
meeting_test_Qwen2.5-32B-Instruct_20251231_123456.json
meeting_test_Qwen2.5-32B-Instruct_20251231_123456.csv
meeting_test_Qwen3-32B_20251231_123456.json
meeting_test_Qwen3-32B_20251231_123456.csv
```

## Evaluation with LLM Judge

After running inference, evaluate the results using the LLM judge:

```bash
# Evaluate Qwen-2.5 results with GPT-5.2
python llm_judge_evaluator.py code_generation_results/meeting_test_Qwen2.5-32B-Instruct_TIMESTAMP.json gpt-5.2

# Evaluate Qwen-3 results with Deepseek-V3
python llm_judge_evaluator.py code_generation_results/meeting_test_Qwen3-32B_TIMESTAMP.json deepseek-v3
```

## Configuration

The script uses these default settings:
- **Cache directory**: `/local-ssd/cek99/hf/transformers/`
- **Max new tokens**: 4096
- **Temperature**: 0.7
- **Execution timeout**: 30 seconds
- **Device map**: "auto" (uses all available GPUs)
- **Data type**: bfloat16 (for memory efficiency)

To modify these, edit the `LocalModelInference` initialization in `local_model_inference.py`.

## Performance Notes

### Model Loading
- First load may take 1-2 minutes (loading ~64GB model into memory)
- Subsequent runs are faster if model stays in memory

### Inference Speed
- Local inference is typically faster than API calls
- Qwen-32B models: ~20-40 tokens/second on A100/H100
- Full 100-problem run: ~30-60 minutes

### GPU Requirements
- **Minimum**: 1x A100 (40GB) or 1x H100 (80GB)
- **Recommended**: 2x A100 or 1x H100 for faster inference
- Models use ~32GB VRAM in bfloat16

## Troubleshooting

### Out of Memory Error

```
RuntimeError: CUDA out of memory
```

**Solution 1: Use 8-bit quantization**
Edit `local_model_inference.py` line 64-65:
```python
self.model = AutoModelForCausalLM.from_pretrained(
    model_name,
    cache_dir=model_cache_dir,
    load_in_8bit=True,  # Add this
    device_map="auto",
    trust_remote_code=True
)
```

**Solution 2: Use smaller batch size**
The script processes one problem at a time by default, so memory should be manageable.

### Model Not Found

```
OSError: Qwen/Qwen3-32B does not appear to be a model identifier
```

**Solution**: Check if model is correctly downloaded and the name is accurate.

### Slow Inference

**Solution 1: Use Flash Attention 2**
```bash
pip install flash-attn --no-build-isolation
```

Then add to model loading:
```python
attn_implementation="flash_attention_2"
```

**Solution 2: Reduce max_new_tokens**
Edit line 46 in `local_model_inference.py`:
```python
max_new_tokens: int = 2048  # Reduce from 4096
```

## Comparison: Local vs API Models

### Advantages of Local Models
- ✓ No API costs
- ✓ No rate limits
- ✓ Full control over generation parameters
- ✓ Data privacy (everything stays local)
- ✓ Faster for large batches

### Disadvantages
- ✗ Requires significant GPU resources
- ✗ Initial model download time
- ✗ May not match performance of GPT-5/o3

## Next Steps

After running local inference:

1. **Compare results** across different models:
   - Qwen-2.5-32B-Instruct
   - Qwen-3-32B
   - GPT-5
   - Deepseek-Reasoner
   - o3-mini

2. **Analyze performance**:
   - Code execution success rate
   - LLM judge evaluation scores
   - Inference speed

3. **Experiment with strategies**:
   - Try different prompting strategies
   - Test zero-shot vs few-shot
   - Adjust temperature and sampling parameters

---

For more information, see:
- `README.md` - General system overview
- `CODE_GENERATION_GUIDE.md` - Code generation details
- `DEEPSEEK_SETUP.md` - Deepseek API models

