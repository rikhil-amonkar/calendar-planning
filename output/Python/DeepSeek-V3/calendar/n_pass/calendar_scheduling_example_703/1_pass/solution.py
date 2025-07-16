from typing import List, Dict, Tuple

def schedule_meeting(participants: List[str], 
                    days: List[str], 
                    work_hours: Tuple[str, str], 
                    duration: int, 
                    schedules: Dict[str, Dict[str, List[Tuple[str, str]]]], 
                    constraints: Dict[str, Dict[str, str]]) -> Tuple[str, str]:
    # Parse work hours
    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Iterate through each day to find a suitable time
    for day in days:
        # Check Stephanie's preference to avoid Monday
        if day == "Monday" and "Stephanie" in constraints and constraints["Stephanie"].get("avoid_day") == "Monday":
            continue
        
        # Collect all busy intervals for the day for all participants
        busy_intervals = []
        for participant in participants:
            if day in schedules[participant]:
                for interval in schedules[participant][day]:
                    start, end = interval
                    busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
        
        # Add additional constraints (e.g., Betty cannot meet on Tuesday after 12:30)
        if day == "Tuesday" and "Betty" in constraints and constraints["Betty"].get("cannot_meet_after") is not None:
            cutoff_time = time_to_minutes(constraints["Betty"]["cannot_meet_after"])
            busy_intervals.append((cutoff_time, work_end_min))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find available slots
        available_slots = []
        prev_end = work_start_min
        
        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if prev_end < work_end_min:
            available_slots.append((prev_end, work_end_min))
        
        # Check for a slot that can fit the duration
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration:
                meeting_start = slot_start
                meeting_end = meeting_start + duration
                return day, f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    
    return None, None

def time_to_minutes(time_str: str) -> int:
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes: int) -> str:
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Input data
participants = ["Stephanie", "Betty"]
days = ["Monday", "Tuesday", "Wednesday"]
work_hours = ("9:00", "17:00")
duration = 60  # minutes

schedules = {
    "Stephanie": {
        "Monday": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"), ("14:00", "14:30")],
        "Tuesday": [("12:00", "13:00")],
        "Wednesday": [("9:00", "10:00"), ("13:00", "14:00")],
    },
    "Betty": {
        "Monday": [("9:00", "10:00"), ("11:00", "11:30"), ("14:30", "15:00"), ("15:30", "16:00")],
        "Tuesday": [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:30", "16:00")],
        "Wednesday": [("10:00", "11:30"), ("12:00", "14:00"), ("14:30", "17:00")],
    }
}

constraints = {
    "Stephanie": {"avoid_day": "Monday"},
    "Betty": {"cannot_meet_after": "12:30"}
}

# Find the meeting time
day, time_range = schedule_meeting(participants, days, work_hours, duration, schedules, constraints)

# Output the result
if day and time_range:
    start_time, end_time = time_range.split(':')
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")