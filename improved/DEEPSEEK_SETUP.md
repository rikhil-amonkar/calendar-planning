# Deepseek Integration Guide

This guide explains how to use Deepseek models with the Natural Plan conversation system.

## Overview

The system now supports both OpenAI and Deepseek models. It automatically detects which API to use based on the model name prefix.

### Supported Deepseek Models

1. **deepseek-v3** - Flagship model for general tasks
2. **deepseek-reasoner** - Reasoning model (similar to OpenAI's o1/o3)

## Setup Instructions

### 1. Get Your Deepseek API Key

1. Visit https://platform.deepseek.com/
2. Create an account or log in
3. Navigate to API Keys section
4. Generate a new API key

### 2. Add API Key to Environment

Edit your `.env` file to include your Deepseek API key:

```bash
OPENAI_API_KEY=your_openai_api_key_here
DEEPSEEK_API_KEY=your_deepseek_api_key_here
```

Or copy from template:
```bash
cp env_template.txt .env
# Then edit .env with your actual keys
```

## Usage Examples

### Code Generation Inference

Run inference with Deepseek models:

**Deepseek-V3 (Flagship):**
```bash
cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate
python code_generation_inference.py deepseek-v3 strategies/my_strategy2.txt meeting 100
```

**Deepseek-Reasoner (Reasoning):**
```bash
python code_generation_inference.py deepseek-reasoner strategies/my_strategy2.txt meeting 100
```

**Quick test with 5 problems:**
```bash
python code_generation_inference.py deepseek-v3 strategies/my_strategy2.txt meeting 5
```

### LLM Judge Evaluation

Use Deepseek models as judges to evaluate results:

```bash
python llm_judge_evaluator.py code_generation_results/meeting_test_gpt-4o-mini_20251231_182108.json deepseek-v3
```

Or with Deepseek-Reasoner as judge:
```bash
python llm_judge_evaluator.py code_generation_results/meeting_test_run.json deepseek-reasoner
```

### Interactive Chat

Start an interactive chat with Deepseek models:

**With Deepseek-V3:**
```bash
python interactive_chat.py deepseek-v3
```

**With Deepseek-Reasoner:**
```bash
python interactive_chat.py deepseek-reasoner
```

Then use commands like:
- `/new meeting 0` - Start conversation about a problem
- `/solution` - Show golden solution
- `/help` - Show all commands

## Technical Details

### Model Detection

The system automatically detects which API to use based on the model name:
- If model starts with `deepseek-` → Uses Deepseek API
- Otherwise → Uses OpenAI API

### Temperature Handling

Some models don't support custom temperature parameters:

**Reasoning models (no custom temperature):**
- `o1`, `o1-mini`, `o3`, `o3-mini` (OpenAI)
- `gpt-5`, `gpt-5.2` (OpenAI)
- `deepseek-reasoner` (Deepseek)

**Standard models (temperature = 0.7 by default):**
- `gpt-3.5-turbo`, `gpt-4`, `gpt-4o`, `gpt-4o-mini` (OpenAI)
- `deepseek-v3` (Deepseek)

The system automatically handles this - no need to worry about it!

### API Endpoint

Deepseek models use the endpoint: `https://api.deepseek.com`

The system uses OpenAI's SDK with a custom base_url, so the API is fully compatible.

## Comparison: OpenAI vs Deepseek

### When to use Deepseek-V3
- Cost-effective alternative to GPT-4
- Strong performance on general tasks
- Good code generation capabilities

### When to use Deepseek-Reasoner
- Complex reasoning problems
- Multi-step logical tasks
- Alternative to o1/o3 models

### When to use OpenAI models
- Latest features (GPT-5.2)
- Specific model requirements
- Established benchmarks

## Results Storage

Results from Deepseek models are saved with the model name in the filename:

```
code_generation_results/meeting_test_deepseek-v3_20251231_123456.json
code_generation_results/meeting_test_deepseek-v3_20251231_123456.csv
code_generation_results/meeting_test_deepseek-reasoner_20251231_123456.json
```

## Troubleshooting

### Error: Missing API Key

```
Error: DEEPSEEK_API_KEY not found in environment
```

**Solution:** Make sure your `.env` file contains `DEEPSEEK_API_KEY=your_key_here`

### Error: Model not found

```
Error code: 404 - {'error': {'message': 'The model `deepseek-xxx` does not exist'}}
```

**Solution:** Check the exact model name. Valid names are:
- `deepseek-v3`
- `deepseek-reasoner`

### Error: Rate limit

```
Error: Rate limit exceeded
```

**Solution:** The LLM judge evaluator includes 1-second delays between calls. For inference, you may need to adjust timing or contact Deepseek support to increase limits.

## Example Workflow

Complete workflow using Deepseek models:

```bash
# 1. Activate environment
cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate

# 2. Run inference with Deepseek-V3
python code_generation_inference.py deepseek-v3 strategies/my_strategy2.txt meeting 100

# 3. Evaluate with GPT-5.2 as judge
python llm_judge_evaluator.py code_generation_results/meeting_test_deepseek-v3_TIMESTAMP.json gpt-5.2

# 4. Or evaluate with Deepseek-Reasoner as judge
python llm_judge_evaluator.py code_generation_results/meeting_test_deepseek-v3_TIMESTAMP.json deepseek-reasoner

# 5. Compare results across different models
```

## Benefits of Multi-Provider Support

1. **Cost Optimization**: Choose more affordable models when appropriate
2. **Redundancy**: Fallback options if one provider has issues
3. **Comparison**: Benchmark different models on same tasks
4. **Flexibility**: Use best model for each specific task type

---

For more information, see:
- [Deepseek Documentation](https://platform.deepseek.com/docs)
- [OpenAI Documentation](https://platform.openai.com/docs)
- `README.md` for general system usage
- `CODE_GENERATION_GUIDE.md` for inference details

