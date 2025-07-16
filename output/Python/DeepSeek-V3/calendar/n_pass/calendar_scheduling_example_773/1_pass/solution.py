from typing import List, Dict, Tuple

def find_earliest_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    work_hours: Tuple[str, str],
    duration_minutes: int
) -> Tuple[str, str]:
    """
    Finds the earliest available meeting time for participants within given constraints.
    
    Args:
        participants: Dictionary of participant names to their busy schedules per day.
        days: List of days to consider (e.g., ["Monday", "Tuesday"]).
        work_hours: Tuple of start and end time in "HH:MM" format (e.g., ("09:00", "17:00")).
        duration_minutes: Duration of the meeting in minutes.
    
    Returns:
        Tuple of (day, time_slot) where time_slot is in "HH:MM-HH:MM" format.
    """
    # Convert work hours to minutes since midnight
    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])
    
    for day in days:
        # Collect all busy intervals for the day across participants
        busy_intervals = []
        for person, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    busy_start = time_to_minutes(start)
                    busy_end = time_to_minutes(end)
                    busy_intervals.append((busy_start, busy_end))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Merge overlapping or adjacent busy intervals
        merged = []
        for start, end in busy_intervals:
            if not merged:
                merged.append([start, end])
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1][1] = max(end, last_end)
                else:
                    merged.append([start, end])
        
        # Check available slots between work hours and busy intervals
        prev_end = work_start
        for start, end in merged:
            if start > prev_end:
                available_duration = start - prev_end
                if available_duration >= duration_minutes:
                    return (day, f"{minutes_to_time(prev_end)}-{minutes_to_time(prev_end + duration_minutes)}")
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if work_end - prev_end >= duration_minutes:
            return (day, f"{minutes_to_time(prev_end)}-{minutes_to_time(prev_end + duration_minutes)}")
    
    return (None, None)

def time_to_minutes(time_str: str) -> int:
    """Converts time string (HH:MM) to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes: int) -> str:
    """Converts minutes since midnight to time string (HH:MM)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules
participants = {
    "Patrick": {},
    "Roy": {
        "Monday": [("10:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("9:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:30"), ("16:30", "17:00")]
    }
}

# Define constraints
days = ["Monday", "Tuesday", "Wednesday"]
work_hours = ("09:00", "17:00")
duration_minutes = 60

# Find the earliest meeting time
day, time_slot = find_earliest_meeting_time(participants, days, work_hours, duration_minutes)

# Output the result
if day and time_slot:
    start, end = time_slot.split('-')
    print(f"{day}: {start}:{end}")
else:
    print("No suitable time found.")