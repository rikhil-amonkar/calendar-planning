from typing import List, Dict, Tuple

def find_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    work_hours: Tuple[str, str],
    duration: int,
    earliest: bool = True
) -> Tuple[str, str]:
    """
    Find a meeting time that fits all participants' schedules.
    
    Args:
        participants: Dictionary of participants and their busy times.
        days: List of days to consider (e.g., ["Monday", "Tuesday"]).
        work_hours: Tuple of work hours (e.g., ("9:00", "17:00")).
        duration: Duration of the meeting in minutes.
        earliest: If True, prioritize the earliest possible time.
    
    Returns:
        Tuple of (day, time_range) where time_range is "HH:MM:HH:MM".
    """
    # Parse work hours
    work_start = convert_time_to_minutes(work_hours[0])
    work_end = convert_time_to_minutes(work_hours[1])
    
    for day in days:
        # Collect all busy intervals for the day
        busy_intervals = []
        for person in participants.values():
            if day in person:
                for start, end in person[day]:
                    busy_start = convert_time_to_minutes(start)
                    busy_end = convert_time_to_minutes(end)
                    busy_intervals.append((busy_start, busy_end))
        
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for start, end in free_slots:
            if end - start >= duration:
                meeting_start = start if earliest else end - duration
                meeting_end = meeting_start + duration
                time_range = (
                    f"{convert_minutes_to_time(meeting_start)}:"
                    f"{convert_minutes_to_time(meeting_end)}"
                )
                return (day, time_range)
    
    return ("", "")

def convert_time_to_minutes(time_str: str) -> int:
    """Convert time string (HH:MM) to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def convert_minutes_to_time(minutes: int) -> str:
    """Convert minutes since midnight to time string (HH:MM)."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define participants' schedules
participants = {
    "Megan": {
        "Monday": [("13:00", "13:30"), ("14:00", "15:30")],
        "Tuesday": [("9:00", "9:30"), ("12:00", "12:30"), ("16:00", "17:00")],
        "Wednesday": [("9:30", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("16:00", "16:30")],
        "Thursday": [("13:30", "14:30"), ("15:00", "15:30")],
    },
    "Daniel": {
        "Monday": [("10:00", "11:30"), ("12:30", "15:00")],
        "Tuesday": [("9:00", "10:00"), ("10:30", "17:00")],
        "Wednesday": [("9:00", "10:00"), ("10:30", "11:30"), ("12:00", "17:00")],
        "Thursday": [("9:00", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
    },
}

# Define meeting constraints
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_hours = ("9:00", "17:00")
duration = 60  # minutes

# Find the earliest meeting time
day, time_range = find_meeting_time(participants, days, work_hours, duration, earliest=True)

# Output the result
print(f"{day}: {time_range}")