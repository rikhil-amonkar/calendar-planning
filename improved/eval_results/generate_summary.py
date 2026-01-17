#!/usr/bin/env python3
"""
Generate comprehensive markdown summary from all constraint evaluation JSON files.
"""

import json
import os
from pathlib import Path
from collections import defaultdict
from datetime import datetime

def parse_filename(filename):
    """Extract model and approach from filename."""
    # Format: meeting_{approach}_{model}_{timestamp}_structured_iterations_constraint_eval.json
    # Remove extension and suffix
    base = filename.replace('_structured_iterations_constraint_eval.json', '')
    parts = base.split('_')
    
    if len(parts) >= 4:
        approach = parts[1]  # python or smt
        
        # Model name is between approach and timestamp (timestamp is last part, usually YYYYMMDD_HHMMSS format)
        # Look for numeric timestamp pattern and take everything before it
        model_parts = []
        for i in range(2, len(parts)):
            # Check if this part looks like a date (starts with YYYYMMDD)
            if parts[i].isdigit() and len(parts[i]) == 8:
                break
            model_parts.append(parts[i])
        
        model = '_'.join(model_parts) if model_parts else 'unknown'
        
        # Clean up model name - replace common separators
        model = model.replace('-', ' ').replace('_', ' ').strip()
        
        # Clean up common model name patterns
        import re
        # Remove date-like patterns (YYYY MM DD) from model names if they appear
        # Pattern: 4 digits, space, 2 digits, space, 2 digits (dates)
        model = re.sub(r'\d{4}\s+\d{2}\s+\d{2}', '', model).strip()
        
        # Title case with exceptions
        words = model.split()
        cleaned_words = []
        for word in words:
            if word.upper() in ['GPT', 'O3', 'SMT']:
                cleaned_words.append(word.upper())
            elif word.lower().startswith('gpt'):
                cleaned_words.append('GPT-' + word[3:].title())
            elif word.lower() == 'o3':
                cleaned_words.append('o3')
            elif word.lower().startswith('deepseek'):
                cleaned_words.append('DeepSeek' + word[8:].title())
            else:
                cleaned_words.append(word.title())
        
        model = ' '.join(cleaned_words).strip()
        
        return approach, model
    return None, None

def load_all_eval_results(eval_results_dir):
    """Load all evaluation JSON files."""
    results = []
    for file in sorted(Path(eval_results_dir).glob('*.json')):
        if 'constraint_eval' in file.name:
            with open(file, 'r') as f:
                data = json.load(f)
                approach, model = parse_filename(file.name)
                results.append({
                    'file': file.name,
                    'approach': approach or 'unknown',
                    'model': model or 'unknown',
                    'summary': data['summary'],
                    'results': data['results']
                })
    return results

def generate_markdown_summary(results):
    """Generate comprehensive markdown summary."""
    md = []
    md.append("# Constraint-Based Evaluation Results Summary")
    md.append("")
    md.append(f"*Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}*")
    md.append("")
    md.append("=" * 80)
    md.append("")
    
    # Overall Summary Table
    md.append("## Overall Summary")
    md.append("")
    md.append("| Model | Approach | Accuracy | Correct/Total | With Plans | No Plans | Successful First Iteration | After Retries | Failed All |")
    md.append("|-------|----------|----------|---------------|------------|----------|-------------------|---------------|------------|")
    
    for r in sorted(results, key=lambda x: (x['approach'], -x['summary']['accuracy'])):
        s = r['summary']
        stats = s['iteration_stats']
        model_display = r['model']
        approach_display = r['approach'].upper()
        accuracy = s['accuracy'] * 100
        first_success = stats.get('problems_successful_first_iteration', stats.get('problems_successful_on_first', 0))
        after_retries = stats['problems_successful_after_retries']
        failed_all = stats['problems_failed_all_iterations']
        
        md.append(f"| {model_display} | {approach_display} | {accuracy:.1f}% | {s['correct']}/{s['total']} | {s['with_plans']} | {s['no_plans']} | {first_success} | {after_retries} | {failed_all} |")
    
    md.append("")
    
    # Top Performers
    md.append("## Top Performers")
    md.append("")
    
    # By accuracy
    sorted_by_accuracy = sorted(results, key=lambda x: -x['summary']['accuracy'])
    md.append("### 🏆 Highest Accuracy")
    md.append("")
    for i, r in enumerate(sorted_by_accuracy[:3], 1):
        s = r['summary']
        model_display = r['model']
        approach_display = r['approach'].upper()
        md.append(f"{i}. **{model_display} ({approach_display})**: {s['accuracy']*100:.1f}% ({s['correct']}/{s['total']})")
    md.append("")
    
    # Best first-iteration execution success
    sorted_by_first = sorted(results, key=lambda x: -x['summary']['iteration_stats'].get('problems_successful_first_iteration', x['summary']['iteration_stats'].get('problems_successful_on_first', 0)))
    md.append("### 🎯 Best First-Iteration Execution Success")
    md.append("")
    for i, r in enumerate(sorted_by_first[:3], 1):
        stats = r['summary']['iteration_stats']
        model_display = r['model']
        approach_display = r['approach'].upper()
        first_success = stats.get('problems_successful_first_iteration', stats.get('problems_successful_on_first', 0))
        first_pct = (first_success / r['summary']['total']) * 100
        md.append(f"{i}. **{model_display} ({approach_display})**: {first_pct:.1f}% ({first_success}/{r['summary']['total']})")
    md.append("")
    
    # Best plan extraction
    sorted_by_plans = sorted(results, key=lambda x: -x['summary']['with_plans'])
    md.append("### 📋 Best Plan Extraction Rate")
    md.append("")
    for i, r in enumerate(sorted_by_plans[:3], 1):
        s = r['summary']
        model_display = r['model']
        approach_display = r['approach'].upper()
        plan_pct = (s['with_plans'] / s['total']) * 100
        md.append(f"{i}. **{model_display} ({approach_display})**: {plan_pct:.1f}% ({s['with_plans']}/{s['total']})")
    md.append("")
    
    # Detailed Breakdown by Approach
    md.append("## Detailed Breakdown by Approach")
    md.append("")
    
    by_approach = defaultdict(list)
    for r in results:
        by_approach[r['approach']].append(r)
    
    for approach in sorted(by_approach.keys()):
        md.append(f"### {approach.upper()} Approach")
        md.append("")
        approach_results = sorted(by_approach[approach], key=lambda x: -x['summary']['accuracy'])
        
        md.append("| Model | Accuracy | Correct | Total | With Plans | No Plans | Avg Iterations | First Iter Success | After Retries |")
        md.append("|-------|----------|---------|-------|------------|----------|----------------|---------------|---------------|")
        
        for r in approach_results:
            s = r['summary']
            stats = s['iteration_stats']
            model_display = r['model']  # Use already cleaned model name
            accuracy = s['accuracy'] * 100
            avg_iter = stats['total_iterations'] / stats['problems_with_iterations'] if stats['problems_with_iterations'] > 0 else 0
            
            first_success = stats.get('problems_successful_first_iteration', stats.get('problems_successful_on_first', 0))
            md.append(f"| {model_display} | {accuracy:.1f}% | {s['correct']} | {s['total']} | {s['with_plans']} | {s['no_plans']} | {avg_iter:.2f} | {first_success} | {stats['problems_successful_after_retries']} |")
        
        md.append("")
    
    # Iteration Statistics
    md.append("## Iteration Statistics")
    md.append("")
    md.append("| Model | Approach | Total Iterations | Avg per Problem | First Iter Success | After Retries | Failed All |")
    md.append("|-------|----------|------------------|-----------------|---------------|---------------|------------|")
    
    for r in sorted(results, key=lambda x: (x['approach'], -x['summary']['accuracy'])):
        stats = r['summary']['iteration_stats']
        model_display = r['model']
        approach_display = r['approach'].upper()
        avg_iter = stats['total_iterations'] / stats['problems_with_iterations'] if stats['problems_with_iterations'] > 0 else 0
        
        first_success = stats.get('problems_successful_first_iteration', stats.get('problems_successful_on_first', 0))
        md.append(f"| {model_display} | {approach_display} | {stats['total_iterations']} | {avg_iter:.2f} | {first_success} | {stats['problems_successful_after_retries']} | {stats['problems_failed_all_iterations']} |")
    
    md.append("")
    
    # Status Breakdown
    md.append("## Status Breakdown")
    md.append("")
    md.append("| Model | Approach | Correct | Wrong Plan | No Plan |")
    md.append("|-------|----------|---------|------------|---------|")
    
    for r in sorted(results, key=lambda x: (x['approach'], -x['summary']['accuracy'])):
        status_count = defaultdict(int)
        for result in r['results']:
            status_count[result['status']] += 1
        
        model_display = r['model']
        approach_display = r['approach'].upper()
        
        md.append(f"| {model_display} | {approach_display} | {status_count['correct']} | {status_count['wrong_plan']} | {status_count.get('no_plan', 0)} |")
    
    md.append("")
    
    # Key Insights
    md.append("## Key Insights")
    md.append("")
    
    # Python vs SMT comparison
    python_results = [r for r in results if r['approach'] == 'python']
    smt_results = [r for r in results if r['approach'] == 'smt']
    
    if python_results and smt_results:
        python_avg = sum(r['summary']['accuracy'] for r in python_results) / len(python_results) * 100
        smt_avg = sum(r['summary']['accuracy'] for r in smt_results) / len(smt_results) * 100
        
        md.append(f"- **Approach Comparison**: Python approach averages {python_avg:.1f}% accuracy, SMT approach averages {smt_avg:.1f}% accuracy")
        md.append("")
    
    # Best improvement from retries
    best_retry_improvement = max(results, key=lambda x: x['summary']['iteration_stats']['problems_successful_after_retries'])
    retry_stats = best_retry_improvement['summary']['iteration_stats']
    md.append(f"- **Best Retry Improvement**: {best_retry_improvement['model']} ({best_retry_improvement['approach'].upper()}) succeeded on {retry_stats['problems_successful_after_retries']} problems after retries")
    md.append("")
    
    # Most reliable (best first-iteration execution)
    most_reliable = max(results, key=lambda x: x['summary']['iteration_stats'].get('problems_successful_first_iteration', x['summary']['iteration_stats'].get('problems_successful_on_first', 0)))
    reliable_stats = most_reliable['summary']['iteration_stats']
    reliable_first_success = reliable_stats.get('problems_successful_first_iteration', reliable_stats.get('problems_successful_on_first', 0))
    reliable_pct = (reliable_first_success / most_reliable['summary']['total']) * 100
    md.append(f"- **Most Reliable**: {most_reliable['model']} ({most_reliable['approach'].upper()}) had successful execution on first iteration {reliable_pct:.1f}% of the time ({reliable_first_success}/{most_reliable['summary']['total']})")
    md.append("")
    
    # Best plan extraction
    best_extraction = max(results, key=lambda x: x['summary']['with_plans'])
    extraction_pct = (best_extraction['summary']['with_plans'] / best_extraction['summary']['total']) * 100
    md.append(f"- **Best Plan Extraction**: {best_extraction['model']} ({best_extraction['approach'].upper()}) extracted plans from {extraction_pct:.1f}% of problems ({best_extraction['summary']['with_plans']}/{best_extraction['summary']['total']})")
    md.append("")
    
    md.append("=" * 80)
    md.append("")
    md.append("*This report summarizes constraint-based evaluations that validate meeting plans against time windows, travel times, and meeting duration requirements.*")
    
    return '\n'.join(md)

if __name__ == '__main__':
    eval_results_dir = Path(__file__).parent
    results = load_all_eval_results(eval_results_dir)
    
    if not results:
        print("No evaluation results found!")
        exit(1)
    
    markdown = generate_markdown_summary(results)
    
    output_file = eval_results_dir / 'EVALUATION_SUMMARY.md'
    with open(output_file, 'w') as f:
        f.write(markdown)
    
    print(f"✓ Generated summary: {output_file}")
    print(f"  Analyzed {len(results)} evaluation results")
