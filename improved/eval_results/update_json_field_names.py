#!/usr/bin/env python3
"""
Update field names in evaluation JSON files to use better terminology.
Changes 'problems_successful_on_first' to 'problems_successful_first_iteration'
"""

import json
from pathlib import Path

def update_json_file(filepath):
    """Update field names in a JSON file."""
    with open(filepath, 'r') as f:
        data = json.load(f)
    
    # Update the field name in iteration_stats
    if 'summary' in data and 'iteration_stats' in data['summary']:
        stats = data['summary']['iteration_stats']
        if 'problems_successful_on_first' in stats:
            # Rename the field
            stats['problems_successful_first_iteration'] = stats.pop('problems_successful_on_first')
    
    # Write back to file
    with open(filepath, 'w') as f:
        json.dump(data, f, indent=2)
    
    return True

if __name__ == '__main__':
    eval_results_dir = Path(__file__).parent
    
    # Find all constraint eval JSON files
    json_files = list(eval_results_dir.glob('*_constraint_eval.json'))
    
    if not json_files:
        print("No evaluation JSON files found!")
        exit(1)
    
    print(f"Updating {len(json_files)} JSON files...")
    
    for json_file in json_files:
        try:
            update_json_file(json_file)
            print(f"✓ Updated: {json_file.name}")
        except Exception as e:
            print(f"✗ Error updating {json_file.name}: {e}")
    
    print(f"\n✓ Completed! Updated {len(json_files)} files.")
