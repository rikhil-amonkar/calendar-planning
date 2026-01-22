# Iterative Pass Results - Bucket Analysis

This document provides a comprehensive analysis of model performance across different constraint difficulty buckets.

## Overall Summary

| Model | Method | Task | Overall Accuracy | Total | Correct |
|-------|--------|------|------------------|-------|---------|
| **GPT-5** | Python | Meeting Planning | 99.00% | 100 | 99 |
| **GPT-5** | SMT | Meeting Planning | 98.00% | 100 | 98 |
| **O3-mini** | Python | Meeting Planning | 96.00% | 100 | 96 |
| **O3-mini** | SMT | Meeting Planning | 99.00% | 100 | 99 |
| **Deepseek-Reasoner** | Python | Meeting Planning | 94.00% | 100 | 94 |
| **Deepseek-Reasoner** | SMT | Meeting Planning | 85.00% | 100 | 85 |
| **Deepseek-Chat** | Python | Meeting Planning | 86.00% | 100 | 86 |
| **Deepseek-Chat** | SMT | Meeting Planning | 53.00% | 100 | 53 |

## Bucket-Level Performance

### Accuracy by Bucket

| Model | Method | Task | 80-100% | 60-80% | 40-60% | 20-40% | 0-20% |
|-------|--------|------|---------|--------|--------|--------|-------|
| **GPT-5** | Python | Meeting Planning | 100.00% | 95.00% | 100.00% | 100.00% | 100.00% |
| **GPT-5** | SMT | Meeting Planning | 100.00% | 95.00% | 100.00% | 100.00% | 95.00% |
| **O3-mini** | Python | Meeting Planning | 90.00% | 90.00% | 100.00% | 100.00% | 100.00% |
| **O3-mini** | SMT | Meeting Planning | 100.00% | 95.00% | 100.00% | 100.00% | 100.00% |
| **Deepseek-Reasoner** | Python | Meeting Planning | 95.00% | 100.00% | 95.00% | 85.00% | 95.00% |
| **Deepseek-Reasoner** | SMT | Meeting Planning | 80.00% | 85.00% | 70.00% | 95.00% | 95.00% |
| **Deepseek-Chat** | Python | Meeting Planning | 80.00% | 90.00% | 80.00% | 80.00% | 100.00% |
| **Deepseek-Chat** | SMT | Meeting Planning | 50.00% | 25.00% | 45.00% | 55.00% | 90.00% |

### Detailed Bucket Statistics

#### GPT-5-Python

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 20 | 100.00% |
| 60-80% | 20 | 19 | 95.00% |
| 40-60% | 20 | 20 | 100.00% |
| 20-40% | 20 | 20 | 100.00% |
| 0-20% | 20 | 20 | 100.00% |

#### GPT-5-SMT

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 20 | 100.00% |
| 60-80% | 20 | 19 | 95.00% |
| 40-60% | 20 | 20 | 100.00% |
| 20-40% | 20 | 20 | 100.00% |
| 0-20% | 20 | 19 | 95.00% |

#### O3-mini-Python

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 18 | 90.00% |
| 60-80% | 20 | 18 | 90.00% |
| 40-60% | 20 | 20 | 100.00% |
| 20-40% | 20 | 20 | 100.00% |
| 0-20% | 20 | 20 | 100.00% |

#### O3-mini-SMT

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 20 | 100.00% |
| 60-80% | 20 | 19 | 95.00% |
| 40-60% | 20 | 20 | 100.00% |
| 20-40% | 20 | 20 | 100.00% |
| 0-20% | 20 | 20 | 100.00% |

#### Deepseek-Reasoner-Python

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 19 | 95.00% |
| 60-80% | 20 | 20 | 100.00% |
| 40-60% | 20 | 19 | 95.00% |
| 20-40% | 20 | 17 | 85.00% |
| 0-20% | 20 | 19 | 95.00% |

#### Deepseek-Reasoner-SMT

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 16 | 80.00% |
| 60-80% | 20 | 17 | 85.00% |
| 40-60% | 20 | 14 | 70.00% |
| 20-40% | 20 | 19 | 95.00% |
| 0-20% | 20 | 19 | 95.00% |

#### Deepseek-Chat-Python

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 16 | 80.00% |
| 60-80% | 20 | 18 | 90.00% |
| 40-60% | 20 | 16 | 80.00% |
| 20-40% | 20 | 16 | 80.00% |
| 0-20% | 20 | 20 | 100.00% |

#### Deepseek-Chat-SMT

| Bucket | Total | Correct | Accuracy |
|--------|-------|---------|----------|
| 80-100% | 20 | 10 | 50.00% |
| 60-80% | 20 | 5 | 25.00% |
| 40-60% | 20 | 9 | 45.00% |
| 20-40% | 20 | 11 | 55.00% |
| 0-20% | 20 | 18 | 90.00% |

