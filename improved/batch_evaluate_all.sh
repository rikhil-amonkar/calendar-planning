#!/bin/bash
# Batch evaluate all files that have LLM judge evaluations

cd /home/cek99/convincing-formalizer
source /home/cek99/venv/bin/activate

CONSTRAINTS_FILE="/home/cek99/formalizer-steering/naturalplan_formalization/data/meeting_planning_100_constraints.json"

echo "========================================================================"
echo "BATCH CONSTRAINT-BASED EVALUATION"
echo "========================================================================"
echo ""

# List of files with LLM judge evaluations (original files, not the _judge_eval ones)
FILES=(
    "code_generation_results/meeting_test_gpt-5_20251224_021226.json"
    "code_generation_results/meeting_test_gpt-4o-mini_20251231_182108.json"
    "code_generation_results/meeting_test_o3-mini_20251231_201401.json"
    "code_generation_results/meeting_test_deepseek-reasoner_20251231_224847.json"
    "code_generation_results/meeting_test_deepseek-chat_20260101_062046.json"
    "code_generation_results/meeting_test_Qwen2_5-32B-Instruct_20260102_133432.json"
    "code_generation_results/meeting_test_Qwen3-32B_20260105_082658.json"
    "code_generation_results/meeting_test_run.json"
)

for file in "${FILES[@]}"; do
    if [ -f "$file" ]; then
        echo "----------------------------------------"
        echo "Processing: $(basename $file)"
        echo "----------------------------------------"
        
        # Convert to structured format
        echo "  1. Converting to structured format..."
        python convert_to_structured_output.py "$file" 2>&1 | tail -n 5
        
        # Evaluate with constraints
        structured_file="${file%.json}_structured.json"
        if [ -f "$structured_file" ]; then
            echo "  2. Evaluating with constraints..."
            python evaluate_structured_outputs.py "$structured_file" "$CONSTRAINTS_FILE" 2>&1 | grep -A 5 "CONSTRAINT-BASED EVALUATION SUMMARY"
        else
            echo "  ERROR: Structured file not created"
        fi
        echo ""
    else
        echo "WARNING: File not found: $file"
    fi
done

echo ""
echo "========================================================================"
echo "BATCH EVALUATION COMPLETE"
echo "========================================================================"
