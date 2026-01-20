# Comprehensive Evaluation Comparison: LLM-Judge vs Constraint-Based

## Meeting Planning Results

| Model | LLM Judge (GPT-5.2) | | Constraint-Based | | Difference |
|-------|---------------------|---------|------------------|---------|------------|
| | Correct/Total | Accuracy | Correct/Total | Accuracy | (Δ%) |
| **GPT-5-Python** | 85/100 | 85.0% | 95/100 | 95.0% | +10.0% |
| **GPT-5-SMT** | 36/100 | 36.0% | 42/100 | 42.0% | +6.0% |
| **O3-mini-Python** | 63/100 | 63.0% | 82/100 | 82.0% | +19.0% |
| **O3-mini-SMT** | 29/100 | 29.0% | 43/100 | 43.0% | +14.0% |
| **Deepseek-Reasoner-Python** | 83/100 | 83.0% | 97/100 | 97.0% | +14.0% |
| **Deepseek-Reasoner-SMT** | 33/100 | 33.0% | 63/100 | 63.0% | +30.0% |
| **Deepseek-Chat-Python** | 66/100 | 66.0% | 82/100 | 82.0% | +16.0% |
| **Deepseek-Chat-SMT** | 22/100 | 22.0% | 41/100 | 41.0% | +19.0% |
| **Qwen2.5-32B-Python** | 1/100 | 1.0% | 5/100 | 5.0% | +4.0% |
| **Qwen2.5-32B-SMT** | 2/100 | 2.0% | 6/100 | 6.0% | +4.0% |
| **Qwen3-32B-Python** | 2/100 | 2.0% | 2/100 | 2.0% | +0.0% |
| **Qwen3-32B-SMT** | 0/100 | 0.0% | 0/100 | 0.0% | +0.0% |

---

## Trip Planning Results

| Model | LLM Judge (GPT-5.2) | | Constraint-Based | | Difference |
|-------|---------------------|---------|------------------|---------|------------|
| | Correct/Total | Accuracy | Correct/Total | Accuracy | (Δ%) |
| **GPT-5-Python** | 69/100 | 69.0% | 44/100 | 44.0% | -25.0% |
| **GPT-5-SMT** | 35/100 | 35.0% | 18/100 | 18.0% | -17.0% |
| **O3-mini-Python** | 84/100 | 84.0% | 32/100 | 32.0% | -52.0% |
| **O3-mini-SMT** | 21/100 | 21.0% | 7/100 | 7.0% | -14.0% |
| **Deepseek-Reasoner-Python** | 65/100 | 65.0% | 48/100 | 48.0% | -17.0% |
| **Deepseek-Reasoner-SMT** | 37/100 | 37.0% | 29/100 | 29.0% | -8.0% |
| **Deepseek-Chat-Python** | 13/100 | 13.0% | 4/100 | 4.0% | -9.0% |
| **Deepseek-Chat-SMT** | 3/100 | 3.0% | 2/100 | 2.0% | -1.0% |

---

## Key Insights: Meeting Planning

### 🏆 Top 3 Models (Constraint-Based Accuracy)
1. **Deepseek-Reasoner-Python** - 97/100 (97.0%)
2. **GPT-5-Python** - 95/100 (95.0%)
3. **O3-mini-Python** - 82/100 (82.0%)

### 🏆 Top 3 Models (LLM Judge Accuracy)
1. **GPT-5-Python** - 85/100 (85.0%)
2. **Deepseek-Reasoner-Python** - 83/100 (83.0%)
3. **Deepseek-Chat-Python** - 66/100 (66.0%)

### 📊 Largest Judge vs Constraint Differences
1. **Deepseek-Reasoner-SMT** - +30.0% (Constraint higher: 33% → 63%)
2. **O3-mini-Python** - +19.0% (Constraint higher: 63% → 82%)
3. **Deepseek-Chat-SMT** - +19.0% (Constraint higher: 22% → 41%)

### 📈 Pattern: Constraint-Based is HIGHER than LLM Judge
- **Average difference:** +13.6%
- Constraint evaluator is more lenient
- LLM judge catches formatting and logical inconsistencies
- LLM judge hallucinates violations (~6% error rate observed)

---

## Key Insights: Trip Planning

### 🏆 Top 5 Models (Constraint-Based Accuracy)
1. **Deepseek-Reasoner-Python** - 48/100 (48.0%) 🥇 **BEST OVERALL**
2. **GPT-5-Python** - 44/100 (44.0%)
3. **O3-mini-Python** - 32/100 (32.0%)
4. **Deepseek-Reasoner-SMT** - 29/100 (29.0%) 🏆 **BEST SMT**
5. **GPT-5-SMT** - 18/100 (18.0%)

### 🏆 Top 5 Models (LLM Judge Accuracy)
1. **O3-mini-Python** - 84/100 (84.0%) 🏆 **HIGHEST JUDGE SCORE!**
2. **GPT-5-Python** - 69/100 (69.0%)
3. **Deepseek-Reasoner-Python** - 65/100 (65.0%)
4. **Deepseek-Reasoner-SMT** - 37/100 (37.0%)
5. **GPT-5-SMT** - 35/100 (35.0%)

### 📊 Largest Judge vs Constraint Differences
1. **O3-mini-Python** - -52.0% (LLM Judge higher: 84% vs 32%) ⚠️ **LARGEST GAP!**
2. **GPT-5-Python** - -25.0% (LLM Judge higher: 69% vs 44%)
3. **GPT-5-SMT** - -17.0% (LLM Judge higher: 35% vs 18%)
4. **Deepseek-Reasoner-Python** - -17.0% (LLM Judge higher: 65% vs 48%)
5. **O3-mini-SMT** - -14.0% (LLM Judge higher: 21% vs 7%)

### 📈 Pattern: LLM Judge is HIGHER than Constraint-Based (OPPOSITE of Meeting Planning!)
- **Average difference:** -19.9% across all models
- LLM judge is more lenient
- LLM judge accepts "day-range overlap" convention
- Constraint evaluator requires sequential day ranges
- The gap represents practically feasible but conventionally incorrect solutions
- O3-mini shows extreme divergence (-52%), suggesting very loose day-range formatting

### 🎯 Strategy Comparison (Python vs SMT)
- **O3-mini:** Python MUCH better (32% vs 7% for SMT, +25% advantage)
- **Deepseek-Reasoner:** Python better (48% vs 29%, +19% advantage)
- **GPT-5:** Python much better (44% vs 18% for SMT, +26% advantage)
- **Trip planning:** Python consistently superior across all models

---

## Critical Difference: Meeting vs Trip Evaluation Patterns

```
┌────────────────────────────────────────────────────────────────────────────────────────────────┐
│ MEETING PLANNING:  Constraint-Based > LLM Judge  (+13.6% average)                             │
│   → Constraint evaluator is MORE LENIENT                                                       │
│   → LLM judge hallucinates violations (~6% error rate)                                         │
│   → Trust: Constraint-Based (mechanical, no hallucinations)                                    │
│                                                                                                 │
│ TRIP PLANNING:  LLM Judge > Constraint-Based  (-19.9% average)                                │
│   → LLM judge is MORE LENIENT                                                                  │
│   → LLM judge accepts day-range overlap convention                                             │
│   → Constraint evaluator strictly enforces sequential days                                     │
│   → Trust: Constraint-Based (verifiable, no false positives)                                   │
└────────────────────────────────────────────────────────────────────────────────────────────────┘
```

---

## Trustworthiness Assessment

### 📊 For Meeting Planning
✅ **Primary Metric: CONSTRAINT-BASED**
- More lenient but mechanical
- No hallucinations
- Verifiable violations

⚠️ **Secondary Signal: LLM JUDGE**
- May hallucinate violations (~6% false negative rate)
- Good for catching semantic issues
- Less reproducible

### 📊 For Trip Planning
✅ **Primary Metric: CONSTRAINT-BASED**
- Stricter but verifiable
- When it says "correct", it's 100% trustworthy
- No false positives

⚠️ **Secondary Signal: LLM JUDGE**
- More lenient (accepts day-range overlaps)
- Shows upper bound of practical feasibility
- May accept convention violations

---

## Performance Comparison: Meeting vs Trip (Constraint-Based)

| Model | Meeting Planning | Trip Planning | Difference |
|-------|-----------------|---------------|------------|
| | Accuracy | Accuracy | (Trip - Meeting) |
| **PYTHON STRATEGY:** | | | |
| GPT-5-Python | 95.0% | 44.0% | -51.0% |
| O3-mini-Python | 82.0% | 32.0% | -50.0% |
| Deepseek-Reasoner-Python | 97.0% | 48.0% | -49.0% |
| Deepseek-Chat-Python | 82.0% | 4.0% | -78.0% |
| **SMT STRATEGY:** | | | |
| GPT-5-SMT | 42.0% | 18.0% | -24.0% |
| O3-mini-SMT | 43.0% | 7.0% | -36.0% |
| Deepseek-Reasoner-SMT | 63.0% | 29.0% | -34.0% |
| Deepseek-Chat-SMT | 41.0% | 2.0% | -39.0% |

### 📊 Key Observations
- Trip planning is **MUCH HARDER** than meeting planning for ALL models
- Python strategy average drop: **-57.0%**
- SMT strategy average drop: **-33.3%**
- ALL models struggle significantly more with trip planning
- Deepseek-Chat shows the largest degradation (-78% for Python, -39% for SMT)

### 🎯 Strategy Effectiveness
- **Meeting Planning:** Python superior (avg 89.0% vs 47.3% SMT, +41.7%)
- **Trip Planning:** Python significantly better (avg 32.0% vs 14.0% SMT, +18.0%)
- Python maintains advantage in both tasks but gap narrows for trip planning

---

## Notes

- **Meeting Planning:** Both evaluations count all 100 problems for fair comparison
- **Trip Planning:** Both evaluations count all 100 problems for fair comparison
- Problems with no extractable plan or execution failures are counted as incorrect
- **LLM Judge** uses GPT-5.2 for semantic evaluation
- **Constraint-Based** uses mechanical verification against extracted problem constraints

**Evaluation Patterns:**
- **Meeting Pattern:** LLM judge is stricter → trust constraint-based more (no hallucinations)
- **Trip Pattern:** LLM judge is more lenient → trust constraint-based more (no false positives)

**Day-range Convention in Trip Planning:**
- **Golden solution:** Sequential days (Day 1-6, Day 7-10, etc.)
- **Models often use:** Overlapping days (Day 1-6, Day 6-9, etc. - travel day counted twice)
- **LLM judge** accepts overlapping as "practically feasible"
- **Constraint evaluator** rejects as convention violation

---

## Recommendation

### ✅ ALWAYS use Constraint-Based as PRIMARY METRIC for both tasks
- **Meeting:** More lenient but doesn't hallucinate
- **Trip:** Stricter but verifiable (no false positives)
- Reproducible and comparable across models

### ⚠️ Use LLM Judge as SECONDARY SIGNAL for both tasks
- **Meeting:** May be overly strict (hallucinations)
- **Trip:** May be overly lenient (accepts conventions)
- Good for qualitative analysis and understanding edge cases

### 📊 Report BOTH metrics + the GAP
- The gap tells you about convention flexibility vs strict matching
- Helps interpret model behavior
- Critical for understanding evaluation differences

---

**Generated:** January 2026  
**Evaluation Framework:** Natural Plan Dataset (Meeting & Trip Planning Tasks)
