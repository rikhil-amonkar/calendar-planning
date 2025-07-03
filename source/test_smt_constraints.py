#!/usr/bin/env python3

import json
import sys
import os

# Add the current directory to path to import from iterative_smt_refinement
sys.path.append('.')

def load_constraints(task):
    """Load constraints from the appropriate JSON file - same as SMT program"""
    task_name_map = {
        "calendar": "calendar_scheduling",
        "trip": "trip_planning",
        "meeting": "meeting_planning"
    }
    with open(f"../data/{task_name_map[task]}_100_constraints.json") as f:
        constraints_data = json.load(f)
        return {example_id: data.get("constraints", {}) 
                for example_id, data in constraints_data.items()}

def test_calendar_constraints():
    """Test calendar constraints extraction"""
    print("=== Testing Calendar Constraints ===")
    
    constraints = load_constraints("calendar")
    
    # Test specific example
    example_id = "calendar_scheduling_example_1"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Meeting duration: {example_constraints.get('meeting_duration')}")
        print(f"Number of disallowed ranges: {len(example_constraints.get('disallowed_ranges', []))}")
        print(f"First disallowed range: {example_constraints.get('disallowed_ranges', [])[0] if example_constraints.get('disallowed_ranges') else 'None'}")
        print()
        
        # Test that meeting_duration is accessible directly
        if 'meeting_duration' in example_constraints:
            print("✓ meeting_duration is accessible directly")
        else:
            print("✗ meeting_duration is NOT accessible directly")
            
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def test_trip_constraints():
    """Test trip constraints extraction"""
    print("=== Testing Trip Constraints ===")
    
    constraints = load_constraints("trip")
    
    # Test specific example
    example_id = "trip_planning_example_142"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Trip length: {example_constraints.get('trip_length')}")
        print(f"Number of city_length entries: {len(example_constraints.get('city_length', []))}")
        print(f"Number of direct_flights: {len(example_constraints.get('direct_flights', []))}")
        print(f"First city_length entry: {example_constraints.get('city_length', [])[0] if example_constraints.get('city_length') else 'None'}")
        print()
        
        # Test that trip_length is accessible directly
        if 'trip_length' in example_constraints:
            print("✓ trip_length is accessible directly")
        else:
            print("✗ trip_length is NOT accessible directly")
            
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def test_meeting_constraints():
    """Test meeting constraints extraction"""
    print("=== Testing Meeting Constraints ===")
    
    constraints = load_constraints("meeting")
    
    # Test specific example
    example_id = "meeting_planning_example_131"
    if example_id in constraints:
        example_constraints = constraints[example_id]
        print(f"Example: {example_id}")
        print(f"Constraints keys: {list(example_constraints.keys())}")
        print(f"Number of people_to_meet: {len(example_constraints.get('people_to_meet', []))}")
        print(f"Number of travel_distances: {len(example_constraints.get('travel_distances', []))}")
        print(f"Start location: {example_constraints.get('start', {}).get('location')}")
        print(f"First person: {example_constraints.get('people_to_meet', [])[0] if example_constraints.get('people_to_meet') else 'None'}")
        print()
        
        # Test that people_to_meet is accessible directly
        if 'people_to_meet' in example_constraints:
            print("✓ people_to_meet is accessible directly")
        else:
            print("✗ people_to_meet is NOT accessible directly")
            
        return example_constraints
    else:
        print(f"✗ Example {example_id} not found in constraints")
        return None

def test_constraint_structure():
    """Test the structure of constraints to understand nesting"""
    print("=== Testing Constraint Structure ===")
    
    # Load raw constraints data to see the original structure
    with open("../data/calendar_scheduling_100_constraints.json") as f:
        raw_data = json.load(f)
    
    example_id = "calendar_scheduling_example_1"
    if example_id in raw_data:
        raw_example = raw_data[example_id]
        print(f"Raw example keys: {list(raw_example.keys())}")
        print(f"Has 'constraints' key: {'constraints' in raw_example}")
        
        if 'constraints' in raw_example:
            nested_constraints = raw_example['constraints']
            print(f"Nested constraints keys: {list(nested_constraints.keys())}")
            print(f"Nested meeting_duration: {nested_constraints.get('meeting_duration')}")
        print()

def test_smt_evaluation_compatibility():
    """Test if the extracted constraints are compatible with SMT evaluation functions"""
    print("=== Testing SMT Evaluation Compatibility ===")
    
    # Import the evaluation functions from SMT file by reading the file directly
    try:
        # Read the SMT file and extract the evaluation functions
        with open('iterative_smt_refinement.py', 'r') as f:
            smt_code = f.read()
        
        # Create a temporary module to test the functions
        import types
        smt_module = types.ModuleType('smt_test')
        
        # Execute the code in the module context, but skip the main execution
        exec(smt_code, smt_module.__dict__)
        
        print("✓ Successfully loaded SMT evaluation functions")
        
        # Test calendar evaluation
        constraints = load_constraints("calendar")
        example_id = "calendar_scheduling_example_1"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            
            # Test with a sample prediction
            test_pred = {
                "day": "Monday",
                "start_time": "14:30",
                "end_time": "15:00"
            }
            
            try:
                result, violations = smt_module.evaluate_calendar(example_constraints, test_pred)
                print(f"✓ Calendar evaluation completed: {result}")
                print(f"  Violations: {violations}")
            except Exception as e:
                print(f"✗ Calendar evaluation failed: {e}")
                import traceback
                traceback.print_exc()
        
        # Test trip evaluation
        constraints = load_constraints("trip")
        example_id = "trip_planning_example_142"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            
            # Test with a sample prediction
            test_pred = {
                "itinerary": [
                    {"day_range": "Day 1-4", "place": "Madrid"},
                    {"day_range": "Day 4-6", "place": "Dublin"},
                    {"day_range": "Day 6-7", "place": "Tallinn"}
                ]
            }
            
            try:
                result, violations = smt_module.evaluate_trip(example_constraints, test_pred)
                print(f"✓ Trip evaluation completed: {result}")
                print(f"  Violations: {violations}")
            except Exception as e:
                print(f"✗ Trip evaluation failed: {e}")
                import traceback
                traceback.print_exc()
        
        # Test meeting evaluation
        constraints = load_constraints("meeting")
        example_id = "meeting_planning_example_131"
        if example_id in constraints:
            example_constraints = constraints[example_id]
            
            # Test with a sample prediction
            test_pred = {
                "itinerary": [
                    {
                        "person": "Jason",
                        "start_time": "10:00",
                        "end_time": "11:30"
                    }
                ]
            }
            
            try:
                result, violations = smt_module.evaluate_meeting(example_constraints, test_pred)
                print(f"✓ Meeting evaluation completed: {result}")
                print(f"  Violations: {violations}")
            except Exception as e:
                print(f"✗ Meeting evaluation failed: {e}")
                import traceback
                traceback.print_exc()
                
    except Exception as e:
        print(f"✗ Failed to test SMT evaluation functions: {e}")
        import traceback
        traceback.print_exc()

def main():
    """Main test function"""
    print("Testing SMT Constraints Extraction")
    print("=" * 50)
    
    # Test constraint structure
    test_constraint_structure()
    
    # Test each task type
    calendar_constraints = test_calendar_constraints()
    trip_constraints = test_trip_constraints()
    meeting_constraints = test_meeting_constraints()
    
    # Test SMT evaluation compatibility
    test_smt_evaluation_compatibility()
    
    print("\n" + "=" * 50)
    print("Test Summary:")
    
    if calendar_constraints and 'meeting_duration' in calendar_constraints:
        print("✓ Calendar constraints: PASSED")
    else:
        print("✗ Calendar constraints: FAILED")
        
    if trip_constraints and 'trip_length' in trip_constraints:
        print("✓ Trip constraints: PASSED")
    else:
        print("✗ Trip constraints: FAILED")
        
    if meeting_constraints and 'people_to_meet' in meeting_constraints:
        print("✓ Meeting constraints: PASSED")
    else:
        print("✗ Meeting constraints: FAILED")

if __name__ == "__main__":
    main() 