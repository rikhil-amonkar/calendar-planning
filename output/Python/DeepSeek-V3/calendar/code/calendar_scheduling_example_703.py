from typing import List, Dict, Tuple

def find_meeting_time(
    participants: List[str],
    schedules: Dict[str, Dict[str, List[Tuple[str, str]]]],
    preferences: Dict[str, Dict[str, str]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str]
) -> Tuple[str, Tuple[str, str]]:
    """
    Find a meeting time that fits all participants' schedules and constraints.
    
    Args:
        participants: List of participant names.
        schedules: Dictionary with participant names as keys and their schedules as values.
                  Schedules are dictionaries with days as keys and list of (start, end) time tuples as values.
        preferences: Dictionary with participant names as keys and their preferences as values.
                    Preferences are dictionaries with keys like "avoid_day" or "cannot_meet_after".
        work_hours: Tuple of (start, end) time for work hours.
        meeting_duration: Duration of the meeting in minutes.
        days: List of days to consider for the meeting.
    
    Returns:
        Tuple of (day, (start_time, end_time)) if a slot is found, otherwise (None, (None, None)).
    """
    # Convert all time strings to minutes since midnight for easier calculations
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = map(time_to_minutes, work_hours)
    duration_minutes = meeting_duration
    
    for day in days:
        # Check if day is avoided by any participant
        avoid_day = False
        for participant in participants:
            if preferences.get(participant, {}).get("avoid_day") == day:
                avoid_day = True
                break
        if avoid_day:
            continue
        
        # Collect all busy intervals for the day
        busy_intervals = []
        for participant in participants:
            for interval in schedules[participant].get(day, []):
                start, end = map(time_to_minutes, interval)
                busy_intervals.append((start, end))
        
        # Also add constraints like "cannot meet after"
        for participant in participants:
            cannot_meet_after = preferences.get(participant, {}).get("cannot_meet_after")
            if cannot_meet_after and day in preferences.get(participant, {}).get("cannot_meet_after_day", day):
                cutoff = time_to_minutes(cannot_meet_after)
                busy_intervals.append((cutoff, work_end))
        
        # Sort intervals by start time
        busy_intervals.sort()
        
        # Find free slots
        prev_end = work_start
        free_slots = []
        for start, end in busy_intervals:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check if any free slot can fit the meeting
        for slot_start, slot_end in free_slots:
            if slot_end - slot_start >= duration_minutes:
                meeting_start = slot_start
                meeting_end = meeting_start + duration_minutes
                return (day, (minutes_to_time(meeting_start), minutes_to_time(meeting_end)))
    
    return (None, (None, None))

# Define the problem
participants = ["Stephanie", "Betty"]
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
    },
}
preferences = {
    "Stephanie": {"avoid_day": "Monday"},
    "Betty": {"cannot_meet_after": "12:30", "cannot_meet_after_day": "Tuesday"},
}
work_hours = ("9:00", "17:00")
meeting_duration = 60  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

# Find the meeting time
day, (start_time, end_time) = find_meeting_time(participants, schedules, preferences, work_hours, meeting_duration, days)

# Output the result
if day:
    print(f"{day}:{start_time}:{end_time}")
else:
    print("No suitable time found.")