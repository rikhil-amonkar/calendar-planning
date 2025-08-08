# Calendar Evaluation Format Fix

## Issue Identified

The `evaluate_calendar` function was **not handling the `time_range` format** correctly, causing plans with valid time ranges to be incorrectly marked as "missing_fields".

### Example 398 Problem

**Model's Prediction:**
```json
{
    "time_range": "13:00:13:30",
    "day": "Monday"
}
```

**Old Evaluation Result:**
```
Constraints satisfied: False
Violated constraints: {"missing_fields": true}
```

**Expected Result:**
```
Constraints satisfied: True
Violated constraints: {}
```

## Root Cause

The `evaluate_calendar` function was expecting `start_time` and `end_time` fields, but the `extract_answer_from_text` function for calendar tasks returns a `time_range` field in the format `"HH:MM:HH:MM"` or `"{HH:MM:HH:MM}"`.

**Format Mismatch:**
- **Expected**: `{"day": "Monday", "start_time": "13:00", "end_time": "13:30"}`
- **Actual**: `{"day": "Monday", "time_range": "13:00:13:30"}`

## Fix Applied

Updated `evaluate_calendar` function to handle both formats:

```python
# Handle time_range format (e.g., "13:00:13:30" or "{13:00:13:30}")
if "time_range" in pred_dict:
    time_range = pred_dict["time_range"]
    # Remove curly braces if present
    if time_range.startswith("{") and time_range.endswith("}"):
        time_range = time_range[1:-1]
    
    # Parse time_range format "HH:MM:HH:MM"
    try:
        # Split by ":" and reconstruct start and end times
        parts = time_range.split(":")
        if len(parts) == 4:  # "HH:MM:HH:MM" format
            pred_start = f"{parts[0]}:{parts[1]}"
            pred_end = f"{parts[2]}:{parts[3]}"
        else:
            return False, {"invalid_time_range_format": time_range}
    except ValueError:
        return False, {"invalid_time_range_format": time_range}

# Handle start_time/end_time format
elif "start_time" in pred_dict and "end_time" in pred_dict:
    pred_start = pred_dict["start_time"]
    pred_end = pred_dict["end_time"]
else:
    return False, {"missing_fields": True}
```

## Files Updated

1. **`source/iterative_plan_refinement_parallel.py`**
   - Updated `evaluate_calendar()` to handle `time_range` format

2. **`source/iterative_plan_refinement_parallel_noConstraintFeedback.py`**
   - Updated `evaluate_calendar()` to handle `time_range` format

3. **`source/iterative_plan_refinement_together.py`**
   - **Inherited fix** through import from `iterative_plan_refinement_parallel.py`

4. **`source/iterative_plan_refinement_together_noConstraintFeedback.py`**
   - **Inherited fix** through import from `iterative_plan_refinement_parallel.py`

## Test Results

### Example 398 (Original Issue)
```
All four files produce identical results:
Constraints satisfied: True
Violated constraints: {}
```

### Format Compatibility Tests
```
✅ time_range format: "13:00:13:30" → Working
✅ time_range with braces: "{13:00:13:30}" → Working  
✅ start_time/end_time format: {"start_time": "13:00", "end_time": "13:30"} → Working
✅ invalid format: "invalid_format" → Properly rejected
```

## Supported Formats

The `evaluate_calendar` function now supports:

1. **`time_range` format**: `"13:00:13:30"` or `"{13:00:13:30}"`
2. **`start_time`/`end_time` format**: `{"start_time": "13:00", "end_time": "13:30"}`
3. **Error handling**: Invalid formats are properly rejected with descriptive error messages

## Impact

1. **Accurate Evaluation**: Calendar predictions with `time_range` format are now correctly evaluated
2. **Backward Compatibility**: Existing `start_time`/`end_time` format continues to work
3. **Better Error Messages**: Invalid formats provide specific error information
4. **Consistent Results**: All four files provide identical evaluation results

## Complete Evaluation Features

The `evaluate_calendar` function now comprehensively validates:

1. ✅ **Format Compatibility**: Handles both `time_range` and `start_time`/`end_time` formats
2. ✅ **Meeting Duration**: Ensures the scheduled time matches the required duration
3. ✅ **Disallowed Ranges**: Checks that the meeting doesn't conflict with blocked times
4. ✅ **Day Validation**: Verifies the meeting is scheduled on the correct day
5. ✅ **Time Parsing**: Robust parsing of various time formats
6. ✅ **Error Handling**: Provides specific error messages for different failure cases

## Conclusion

The calendar evaluation format fix ensures that the evaluation system correctly handles the `time_range` format used by the `extract_answer_from_text` function. This resolves the "missing_fields" error and provides accurate constraint validation for calendar scheduling tasks.

**The issue reported in example 398 is now properly fixed across all four files.** 