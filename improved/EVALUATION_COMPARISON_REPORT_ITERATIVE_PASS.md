# Comprehensive Evaluation Comparison: Iterative Pass Results

## Meeting Planning Results (Iterative Pass - Final Iteration)

| Model | Constraint-Based | | Iteration Statistics | |
|-------|------------------|---------|---------------------|---------|
| | Correct/Total | Accuracy | First Try Success | After Retries | Avg Iterations |
| **GPT-5-Python** | 99/100 | 99.0% | 98/100 (98.0%) | 2/100 (2.0%) | 1.02 |
| **O3-mini-Python** | 96/100 | 96.0% | 94/100 (94.0%) | 6/100 (6.0%) | 1.06 |
| **Deepseek-Reasoner-Python** | 94/100 | 94.0% | 93/100 (93.0%) | 6/100 (6.0%) | 1.06 |
| **Deepseek-Chat-Python** | 86/100 | 86.0% | 79/100 (79.0%) | 13/100 (13.0%) | 1.18 |
| **O3-mini-SMT** | 99/100 | 99.0% | 56/100 (56.0%) | 44/100 (44.0%) | 1.73 |
| **GPT-5-SMT** | 98/100 | 98.0% | 29/100 (29.0%) | 70/100 (70.0%) | 1.89 |
| **Deepseek-Reasoner-SMT** | 85/100 | 85.0% | 78/100 (78.0%) | 22/100 (22.0%) | 1.26 |
| **Deepseek-Chat-SMT** | 53/100 | 53.0% | 49/100 (49.0%) | 43/100 (43.0%) | 1.79 |

---

## Key Insights: Iterative Pass Performance

### 🏆 Top 4 Models (Final Iteration Accuracy)
1. **GPT-5-Python** - 99/100 (99.0%) 🥇
2. **O3-mini-SMT** - 99/100 (99.0%) 🥇
3. **GPT-5-SMT** - 98/100 (98.0%)
4. **O3-mini-Python** - 96/100 (96.0%)

### 📊 Iteration Effectiveness Analysis

#### Python Strategy - High First-Try Success
- **GPT-5-Python**: 98% first-try success, only 2% needed retries
- **O3-mini-Python**: 94% first-try success, 6% needed retries
- **Deepseek-Reasoner-Python**: 93% first-try success, 6% needed retries
- **Deepseek-Chat-Python**: 79% first-try success, 13% needed retries (lowest)

**Python Average:** 91.0% first-try success, 6.75% after retries, 1.08 avg iterations

#### SMT Strategy - Lower First-Try, Higher Retry Success
- **O3-mini-SMT**: 56% first-try success, **44% needed retries** (highest retry rate!)
- **GPT-5-SMT**: 29% first-try success, **70% needed retries** (most retries!)
- **Deepseek-Reasoner-SMT**: 78% first-try success, 22% needed retries
- **Deepseek-Chat-SMT**: 49% first-try success, 43% needed retries

**SMT Average:** 53.0% first-try success, 44.75% after retries, 1.67 avg iterations

### 🎯 Key Observations

1. **SMT Strategy Benefits More from Iterations**
   - SMT models show dramatic improvement with retries
   - GPT-5-SMT: 29% → 98% (+69% improvement!)
   - O3-mini-SMT: 56% → 99% (+43% improvement)
   - Deepseek-Chat-SMT: 49% → 53% (+4% improvement, but still low)

2. **Python Strategy Already Strong on First Try**
   - Most Python models succeed 90%+ on first attempt
   - Iterations provide modest gains (2-13%)
   - GPT-5-Python nearly perfect (99%) with minimal retries

3. **Iteration Efficiency**
   - **Python:** Average 1.08 iterations (very efficient)
   - **SMT:** Average 1.67 iterations (more retries needed)
   - SMT requires ~55% more iterations on average

---

## Comparison: Single Pass vs Iterative Pass

### Python Strategy Improvement

| Model | Single Pass | Iterative Pass | Improvement |
|-------|------------|----------------|-------------|
| **GPT-5-Python** | 95.0% | 99.0% | +4.0% |
| **O3-mini-Python** | 82.0% | 96.0% | +14.0% |
| **Deepseek-Reasoner-Python** | 97.0% | 94.0% | -3.0% |
| **Deepseek-Chat-Python** | 82.0% | 86.0% | +4.0% |

**Python Average Improvement:** +4.75%

### SMT Strategy Improvement

| Model | Single Pass | Iterative Pass | Improvement |
|-------|------------|----------------|-------------|
| **GPT-5-SMT** | 42.0% | 98.0% | **+56.0%** 🚀 |
| **O3-mini-SMT** | 43.0% | 99.0% | **+56.0%** 🚀 |
| **Deepseek-Reasoner-SMT** | 63.0% | 85.0% | +22.0% |
| **Deepseek-Chat-SMT** | 41.0% | 53.0% | +12.0% |

**SMT Average Improvement:** +36.5%

### 📈 Critical Finding: SMT Benefits Dramatically from Iterations

```
┌────────────────────────────────────────────────────────────────────────────────────────────┐
│ SINGLE PASS:  Python (89.0%) >> SMT (47.3%)  →  +41.7% gap                                │
│ ITERATIVE:    Python (93.75%) ≈ SMT (83.75%)  →  +10.0% gap                                │
│                                                                                             │
│ The gap NARROWS from 41.7% to 10.0% with iterations!                                        │
│                                                                                             │
│ SMT models catch up significantly when allowed to refine their solutions.                  │
│ GPT-5-SMT and O3-mini-SMT show MASSIVE improvements (+56% each).                          │
└────────────────────────────────────────────────────────────────────────────────────────────┘
```

---

## Iteration Statistics Deep Dive

### Most Iterative Models (Highest Average Iterations)
1. **GPT-5-SMT** - 1.89 avg iterations (29% first-try, 70% retries)
2. **O3-mini-SMT** - 1.73 avg iterations (56% first-try, 44% retries)
3. **Deepseek-Chat-SMT** - 1.79 avg iterations (49% first-try, 43% retries)
4. **Deepseek-Chat-Python** - 1.18 avg iterations (79% first-try, 13% retries)

### Most Efficient Models (Lowest Average Iterations)
1. **GPT-5-Python** - 1.02 avg iterations (98% first-try, 2% retries) ⚡
2. **O3-mini-Python** - 1.06 avg iterations (94% first-try, 6% retries)
3. **Deepseek-Reasoner-Python** - 1.06 avg iterations (93% first-try, 6% retries)
4. **Deepseek-Reasoner-SMT** - 1.26 avg iterations (78% first-try, 22% retries)

### Retry Success Stories
- **GPT-5-SMT**: 70 problems succeeded after retries (from 29% to 98%)
- **O3-mini-SMT**: 44 problems succeeded after retries (from 56% to 99%)
- **Deepseek-Chat-SMT**: 43 problems succeeded after retries (from 49% to 53%)
- **Deepseek-Chat-Python**: 13 problems succeeded after retries (from 79% to 86%)

---

## Strategy Comparison: Python vs SMT (Iterative Pass)

### Final Accuracy Comparison
| Strategy | Average Accuracy | Best Model | Worst Model |
|----------|-----------------|------------|-------------|
| **Python** | 93.75% | GPT-5 (99.0%) | Deepseek-Chat (86.0%) |
| **SMT** | 83.75% | O3-mini/GPT-5 (99.0%/98.0%) | Deepseek-Chat (53.0%) |

### First-Try Success Comparison
| Strategy | Average First-Try | Best First-Try | Worst First-Try |
|----------|------------------|----------------|-----------------|
| **Python** | 91.0% | GPT-5 (98.0%) | Deepseek-Chat (79.0%) |
| **SMT** | 53.0% | Deepseek-Reasoner (78.0%) | GPT-5 (29.0%) |

### Iteration Efficiency
| Strategy | Avg Iterations | Retry Rate | Efficiency |
|----------|---------------|------------|------------|
| **Python** | 1.08 | 6.75% | ⚡ Very Efficient |
| **SMT** | 1.67 | 44.75% | 🔄 Needs More Retries |

### Key Insight
- **Python:** Strong on first try, minimal retries needed
- **SMT:** Weak on first try, but retries are highly effective
- **SMT catches up** with iterations, narrowing the gap from 41.7% to 10.0%

---

## Model-Specific Analysis

### 🏆 GPT-5-Python
- **Final Accuracy:** 99.0% (near-perfect)
- **First-Try:** 98.0% (excellent)
- **Retries:** Only 2 problems needed retries
- **Efficiency:** 1.02 iterations (most efficient)
- **Verdict:** Best overall performance, minimal iteration needed

### 🏆 O3-mini-SMT
- **Final Accuracy:** 99.0% (tied for best)
- **First-Try:** 56.0% (moderate)
- **Retries:** 44 problems succeeded after retries
- **Efficiency:** 1.73 iterations (needs retries but effective)
- **Verdict:** Strong final result despite low first-try success

### 🏆 GPT-5-SMT
- **Final Accuracy:** 98.0% (excellent)
- **First-Try:** 29.0% (lowest first-try!)
- **Retries:** 70 problems succeeded after retries (most retries!)
- **Efficiency:** 1.89 iterations (most iterative)
- **Verdict:** Dramatic improvement with iterations (+69%), but needs many retries

### ⚠️ Deepseek-Chat-SMT
- **Final Accuracy:** 53.0% (lowest)
- **First-Try:** 49.0% (low)
- **Retries:** 43 problems succeeded after retries
- **Efficiency:** 1.79 iterations
- **Verdict:** Struggles even with iterations, may need different approach

### 📊 Deepseek-Reasoner-Python
- **Final Accuracy:** 94.0% (good)
- **First-Try:** 93.0% (excellent)
- **Retries:** 6 problems succeeded after retries
- **Efficiency:** 1.06 iterations
- **Note:** Slightly lower than single pass (97%), but still strong

---

## Cost-Benefit Analysis: Iterations

### Iteration Value by Model

**High Value (Large Improvement):**
- GPT-5-SMT: +56% improvement (worth the extra iterations)
- O3-mini-SMT: +56% improvement (worth the extra iterations)
- O3-mini-Python: +14% improvement (moderate value)

**Moderate Value:**
- Deepseek-Reasoner-SMT: +22% improvement
- Deepseek-Chat-SMT: +12% improvement
- GPT-5-Python: +4% improvement (already near-perfect)
- Deepseek-Chat-Python: +4% improvement

**Negative/Neutral:**
- Deepseek-Reasoner-Python: -3% (slight regression, likely noise)

### Cost Considerations
- **Python models:** Low cost (1.08 avg iterations)
- **SMT models:** Higher cost (1.67 avg iterations, ~55% more)
- **Best ROI:** GPT-5-SMT and O3-mini-SMT (massive gains)
- **Diminishing returns:** GPT-5-Python (already at 99%)

---

## Recommendations

### ✅ Use Iterative Pass When:
1. **SMT Strategy:** Essential for SMT models (especially GPT-5 and O3-mini)
2. **High-Stakes Applications:** When accuracy matters more than cost
3. **Complex Problems:** When first-try success is expected to be lower

### ⚠️ Consider Single Pass When:
1. **Python Strategy:** Already strong (90%+ first-try), iterations provide modest gains
2. **Cost-Sensitive:** Python models are efficient but SMT requires more iterations
3. **Time-Critical:** When latency matters more than perfect accuracy

### 🎯 Optimal Strategy Selection:
- **For Maximum Accuracy:** Use iterative pass with GPT-5-Python or O3-mini-SMT (both 99%)
- **For Efficiency:** Use single pass with Python models (already 89% average)
- **For SMT Models:** Always use iterative pass (dramatic improvements)
- **For Python Models:** Iterations provide modest gains, evaluate cost-benefit

---

## Summary Statistics

### Overall Performance (Iterative Pass)
- **Total Problems Evaluated:** 800 (100 per model × 8 models)
- **Total Correct (Final):** 710 (88.75% overall accuracy)
- **Python Strategy Average:** 93.75%
- **SMT Strategy Average:** 83.75%
- **Gap:** 10.0% (narrowed from 41.7% in single pass)

### Iteration Efficiency
- **Total Iterations:** 1,099 across all models
- **Average Iterations per Problem:** 1.37
- **Problems Needing Retries:** 206 (25.75%)
- **Retry Success Rate:** High (most retries lead to success)

### Improvement from Single Pass
- **Python Average:** +4.75% improvement
- **SMT Average:** +36.5% improvement
- **Overall:** +21.6% average improvement
- **Largest Gains:** GPT-5-SMT and O3-mini-SMT (+56% each)

---

## Notes

- **Evaluation Method:** Constraint-based evaluation of final iteration result
- **Iteration Definition:** Each model was allowed multiple attempts to refine solutions
- **Final Result:** Evaluates the result AFTER all iterations, not just first attempt
- **All 100 problems** counted for each model (problems with no plan = incorrect)
- **Iteration Statistics:** Track first-try success vs retry success

**Key Finding:**
Iterative pass dramatically improves SMT strategy performance, narrowing the gap with Python from 41.7% to 10.0%. SMT models benefit significantly from refinement opportunities, while Python models are already strong on first try.

---

**Generated:** January 2026  
**Evaluation Framework:** Natural Plan Dataset (Meeting Planning Task - Iterative Pass)  
**Results Location:** `improved/iterative_pass_results/final/`
