#!/usr/bin/env python3
"""
Extract constraints from meeting_test.json and convert to the format expected by evaluate_by_constraint.py
"""

import json
import sys
import ast
from pathlib import Path
from typing import Dict, List


def parse_time_to_minutes(time_str: str) -> int:
    """Convert time string like '9:00AM' to minutes since midnight."""
    time_str = time_str.strip()
    
    # Handle AM/PM
    if 'AM' in time_str or 'PM' in time_str:
        is_pm = 'PM' in time_str
        time_str = time_str.replace('AM', '').replace('PM', '').strip()
        
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        
        # Convert to 24-hour
        if is_pm and hour != 12:
            hour += 12
        elif not is_pm and hour == 12:
            hour = 0
        
        return hour * 60 + minute
    else:
        # Assume 24-hour format
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return hour * 60 + minute


def format_time_for_eval(minutes: int) -> str:
    """Convert minutes since midnight to HH:MM format for evaluation."""
    hour = minutes // 60
    minute = minutes % 60
    
    if hour >= 12:
        if hour > 12:
            hour -= 12
        period = 'PM'
    else:
        if hour == 0:
            hour = 12
        period = 'AM'
    
    return f"{hour}:{minute:02d}{period}"


def parse_constraints(constraints_str: str, dist_matrix_str: str) -> Dict:
    """
    Parse constraint string and distance matrix into structured format.
    
    Args:
        constraints_str: String like "[[\"Richmond District\", \"9:00AM\"], [\"Betty\", \"Financial District\", \"5:15PM to 9:45PM\", 60]]"
        dist_matrix_str: String like "{\"Richmond District\": {\"Financial District\": 22}, ...}"
    
    Returns:
        Dictionary with structured constraints
    """
    # Parse the constraint list
    constraints_list = ast.literal_eval(constraints_str)
    
    # Parse distance matrix
    dist_matrix = json.loads(dist_matrix_str)
    
    # First element is always start location and time
    start_location, start_time = constraints_list[0]
    
    # Build list of people to meet
    people_to_meet = []
    for item in constraints_list[1:]:
        person_name = item[0]
        location = item[1]
        time_range = item[2]  # e.g., "5:15PM to 9:45PM"
        min_duration = item[3]
        
        # Parse time range
        time_parts = time_range.split(' to ')
        from_time = time_parts[0].strip()
        to_time = time_parts[1].strip()
        
        people_to_meet.append({
            "name": person_name,
            "location": location,
            "time_of_day": {
                "from": format_time_for_eval(parse_time_to_minutes(from_time)),
                "to": format_time_for_eval(parse_time_to_minutes(to_time))
            },
            "min_duration": min_duration
        })
    
    # Build travel distances
    travel_distances = []
    for from_loc, destinations in dist_matrix.items():
        for to_loc, time in destinations.items():
            travel_distances.append({
                "place": {
                    "from": from_loc,
                    "to": to_loc
                },
                "walking_time": time
            })
    
    return {
        "start": {
            "location": start_location,
            "time_of_day": format_time_for_eval(parse_time_to_minutes(start_time))
        },
        "people_to_meet": people_to_meet,
        "travel_distances": travel_distances
    }


def extract_all_constraints(meeting_test_file: str, output_file: str = None) -> None:
    """
    Extract all constraints from meeting_test.json
    
    Args:
        meeting_test_file: Path to meeting_test.json
        output_file: Output path (optional)
    """
    with open(meeting_test_file, 'r') as f:
        data = json.load(f)
    
    print(f"✓ Loaded {len(data)} problems from {meeting_test_file}")
    
    # Extract constraints for each problem
    all_constraints = {}
    for item in data:
        problem_id = item['id']
        constraints_str = item['constraints']
        dist_matrix_str = item['dist_matrix']
        
        try:
            constraints = parse_constraints(constraints_str, dist_matrix_str)
            all_constraints[problem_id] = {
                "constraints": constraints
            }
        except Exception as e:
            print(f"  Warning: Failed to parse {problem_id}: {e}")
    
    print(f"✓ Successfully extracted {len(all_constraints)} constraint sets")
    
    # Determine output path
    if output_file:
        output_path = Path(output_file)
    else:
        output_path = Path(meeting_test_file).parent / "meeting_planning_100_constraints.json"
    
    # Save
    with open(output_path, 'w') as f:
        json.dump(all_constraints, f, indent=2)
    
    print(f"✓ Saved constraints to: {output_path}")
    
    # Show sample
    sample_id = list(all_constraints.keys())[0]
    print(f"\nSample constraint for {sample_id}:")
    print(json.dumps(all_constraints[sample_id], indent=2)[:500])


def main():
    """Main function."""
    if len(sys.argv) < 2:
        print("Usage: python extract_meeting_constraints.py <meeting_test.json> [output.json]")
        print("\nArguments:")
        print("  meeting_test.json : Path to meeting_test.json from Natural Plan dataset")
        print("  output.json       : Output path (optional, defaults to meeting_planning_100_constraints.json)")
        print("\nExample:")
        print("  python extract_meeting_constraints.py /path/to/meeting_test.json")
        sys.exit(1)
    
    meeting_test_file = sys.argv[1]
    output_file = sys.argv[2] if len(sys.argv) > 2 else None
    
    if not Path(meeting_test_file).exists():
        print(f"Error: File not found: {meeting_test_file}")
        sys.exit(1)
    
    extract_all_constraints(meeting_test_file, output_file)
    
    print("\n" + "="*70)
    print("EXTRACTION COMPLETE")
    print("="*70)


if __name__ == "__main__":
    main()
