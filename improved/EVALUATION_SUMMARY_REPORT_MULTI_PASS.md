# Constraint-Based Evaluation Results Summary

*Generated: 2026-01-17 19:28:00*

================================================================================

## Overall Summary

| Model | Approach | Accuracy | Correct/Total | With Plans | No Plans | Successful First Iteration | After Retries | Failed All |
|-------|----------|----------|---------------|------------|----------|-------------------|---------------|------------|
| DeepSeek Reasoner | PYTHON | 57.0% | 57/100 | 98 | 2 | 94 | 4 | 2 |
| O3 Mini | PYTHON | 56.0% | 56/100 | 99 | 1 | 95 | 4 | 1 |
| GPT 5 | PYTHON | 55.0% | 55/100 | 100 | 0 | 98 | 2 | 0 |
| DeepSeek Chat | PYTHON | 52.0% | 52/100 | 88 | 12 | 82 | 6 | 12 |
| GPT 5 | SMT | 49.0% | 49/100 | 87 | 13 | 38 | 49 | 13 |
| DeepSeek Chat | SMT | 43.0% | 43/100 | 83 | 17 | 48 | 35 | 17 |
| DeepSeek Reasoner | SMT | 41.0% | 41/100 | 91 | 9 | 68 | 23 | 9 |
| O3 Mini | SMT | 34.0% | 34/100 | 72 | 28 | 48 | 24 | 28 |

## Top Performers

### 🏆 Highest Accuracy

1. **DeepSeek Reasoner (PYTHON)**: 57.0% (57/100)
2. **O3 Mini (PYTHON)**: 56.0% (56/100)
3. **GPT 5 (PYTHON)**: 55.0% (55/100)

### 🎯 Best First-Iteration Execution Success

1. **GPT 5 (PYTHON)**: 98.0% (98/100)
2. **O3 Mini (PYTHON)**: 95.0% (95/100)
3. **DeepSeek Reasoner (PYTHON)**: 94.0% (94/100)

### 📋 Best Plan Extraction Rate

1. **GPT 5 (PYTHON)**: 100.0% (100/100)
2. **O3 Mini (PYTHON)**: 99.0% (99/100)
3. **DeepSeek Reasoner (PYTHON)**: 98.0% (98/100)

## Detailed Breakdown by Approach

### PYTHON Approach

| Model | Accuracy | Correct | Total | With Plans | No Plans | Avg Iterations | First Iter Success | After Retries |
|-------|----------|---------|-------|------------|----------|----------------|---------------|---------------|
| DeepSeek Reasoner | 57.0% | 57 | 100 | 98 | 2 | 1.04 | 94 | 4 |
| O3 Mini | 56.0% | 56 | 100 | 99 | 1 | 1.04 | 95 | 4 |
| GPT 5 | 55.0% | 55 | 100 | 100 | 0 | 1.02 | 98 | 2 |
| DeepSeek Chat | 52.0% | 52 | 100 | 88 | 12 | 1.10 | 82 | 6 |

### SMT Approach

| Model | Accuracy | Correct | Total | With Plans | No Plans | Avg Iterations | First Iter Success | After Retries |
|-------|----------|---------|-------|------------|----------|----------------|---------------|---------------|
| GPT 5 | 49.0% | 49 | 100 | 87 | 13 | 1.88 | 38 | 49 |
| DeepSeek Chat | 43.0% | 43 | 100 | 83 | 17 | 1.57 | 48 | 35 |
| DeepSeek Reasoner | 41.0% | 41 | 100 | 91 | 9 | 1.57 | 68 | 23 |
| O3 Mini | 34.0% | 34 | 100 | 72 | 28 | 2.28 | 48 | 24 |

## Iteration Statistics

| Model | Approach | Total Iterations | Avg per Problem | First Iter Success | After Retries | Failed All |
|-------|----------|------------------|-----------------|---------------|---------------|------------|
| DeepSeek Reasoner | PYTHON | 104 | 1.04 | 94 | 4 | 2 |
| O3 Mini | PYTHON | 104 | 1.04 | 95 | 4 | 1 |
| GPT 5 | PYTHON | 102 | 1.02 | 98 | 2 | 0 |
| DeepSeek Chat | PYTHON | 110 | 1.10 | 82 | 6 | 12 |
| GPT 5 | SMT | 188 | 1.88 | 38 | 49 | 13 |
| DeepSeek Chat | SMT | 157 | 1.57 | 48 | 35 | 17 |
| DeepSeek Reasoner | SMT | 157 | 1.57 | 68 | 23 | 9 |
| O3 Mini | SMT | 228 | 2.28 | 48 | 24 | 28 |

## Status Breakdown

| Model | Approach | Correct | Wrong Plan | No Plan |
|-------|----------|---------|------------|---------|
| DeepSeek Reasoner | PYTHON | 57 | 41 | 2 |
| O3 Mini | PYTHON | 56 | 43 | 1 |
| GPT 5 | PYTHON | 55 | 45 | 0 |
| DeepSeek Chat | PYTHON | 52 | 36 | 12 |
| GPT 5 | SMT | 49 | 38 | 13 |
| DeepSeek Chat | SMT | 43 | 40 | 17 |
| DeepSeek Reasoner | SMT | 41 | 50 | 9 |
| O3 Mini | SMT | 34 | 38 | 28 |

## Key Insights

- **Approach Comparison**: Python approach averages 55.0% accuracy, SMT approach averages 41.8% accuracy

- **Best Retry Improvement**: GPT 5 (SMT) succeeded on 49 problems after retries

- **Most Reliable**: GPT 5 (PYTHON) had successful execution on first iteration 98.0% of the time (98/100)

- **Best Plan Extraction**: GPT 5 (PYTHON) extracted plans from 100.0% of problems (100/100)

================================================================================

*This report summarizes constraint-based evaluations that validate meeting plans against time windows, travel times, and meeting duration requirements.*