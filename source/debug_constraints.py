#!/usr/bin/env python3

import json

def load_constraints(task):
    """Load constraints for the specified task"""
    if task == "calendar":
        with open("../data/calendar_scheduling_100_constraints.json", 'r') as f:
            return json.load(f)
    elif task == "meeting":
        with open("../data/meeting_planning_100_constraints.json", 'r') as f:
            return json.load(f)
    elif task == "trip":
        with open("../data/trip_planning_100_constraints.json", 'r') as f:
            return json.load(f)
    else:
        raise ValueError(f"Unknown task: {task}")

def evaluate_calendar(constraints, pred_dict):
    """Evaluate calendar constraints comprehensively"""
    # Check for missing fields
    if not pred_dict or "day" not in pred_dict or "time_range" not in pred_dict:
        return False, {"missing_fields": True}

    pred_day = pred_dict["day"]
    time_range = pred_dict["time_range"]
    
    # Check for None values
    if pred_day is None or time_range is None:
        return False, {"null_fields": True}
    
    # Parse time range
    try:
        time_range = time_range.replace("{", "").replace("}", "")
        parts = time_range.split(":")
        if len(parts) == 4:
            # Format: HH:MM:HH:MM
            start_time = float(parts[0]) + float(parts[1]) / 60
            end_time = float(parts[2]) + float(parts[3]) / 60
        else:
            return False, {"unparsable_time": True}
    except (ValueError, IndexError):
        return False, {"unparsable_time": True}

    # Check meeting duration - handle nested constraints structure
    actual_constraints = constraints.get("constraints", constraints)
    meeting_duration = actual_constraints.get("meeting_duration")
    if meeting_duration is None:
        # Default to 1.0 if we can't determine
        meeting_duration = 1.0
    
    actual_duration = end_time - start_time
    if abs(actual_duration - meeting_duration) > 0.01:
        return False, {"meeting_duration": {"required": meeting_duration, "actual": actual_duration}}

    # Check disallowed time ranges
    for disallowed_range in actual_constraints.get("disallowed_ranges", []):
        if disallowed_range["day"] == pred_day:
            if (start_time >= disallowed_range["start"] and start_time < disallowed_range["end"]) or \
                    (end_time > disallowed_range["start"] and end_time <= disallowed_range["end"]) or \
                    (start_time <= disallowed_range["start"] and end_time >= disallowed_range["end"]):
                return False, {"time_conflict": disallowed_range}
    
    # Check work hours (9:00-17:00)
    if start_time < 9.0 or end_time > 17.0:
        return False, {"work_hours": {"start": 9.0, "end": 17.0}}
    
    return True, {}

if __name__ == "__main__":
    # Load constraints
    constraints = load_constraints("calendar")
    
    # Get specific example
    example_constraints = constraints.get("calendar_scheduling_example_1", {})
    print(f"Example constraints: {example_constraints}")
    print(f"Meeting duration: {example_constraints.get('meeting_duration')}")
    
    # Test with the prediction from the user's output
    pred_dict = {
        "time_range": "{09:30:10:00}",
        "day": "Monday"
    }
    
    print("\nTesting evaluation:")
    result, violations = evaluate_calendar(example_constraints, pred_dict)
    print(f"Result: {result}")
    print(f"Violations: {violations}")
    
    # Test with the correct gold answer
    gold_pred_dict = {
        "time_range": "{14:30:15:00}",
        "day": "Monday"
    }
    
    print("\nTesting with gold answer:")
    result, violations = evaluate_calendar(example_constraints, gold_pred_dict)
    print(f"Result: {result}")
    print(f"Violations: {violations}") 