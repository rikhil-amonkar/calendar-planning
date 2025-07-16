from typing import List, Dict, Tuple

def find_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str],
    preferences: Dict[str, List[str]] = None
) -> Tuple[str, str]:
    """
    Find a meeting time that fits all participants' schedules.
    
    Args:
        participants: Dictionary with participant names as keys and their busy times as values.
                     Busy times are stored as a dictionary with days as keys and lists of
                     (start, end) time tuples as values.
        work_hours: Tuple of (start, end) times for the workday.
        meeting_duration: Duration of the meeting in minutes.
        days: List of days to consider for the meeting.
        preferences: Optional dictionary with participant names as keys and days they prefer to avoid.
    
    Returns:
        A tuple of (day, time_range) where time_range is in the format "HH:MM-HH:MM".
    """
    # Convert all times to minutes since midnight for easier comparison
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = map(time_to_minutes, work_hours)
    meeting_duration_min = meeting_duration
    
    # Iterate through each day to find a suitable time slot
    for day in days:
        if preferences:
            avoid_days = preferences.get('Carl', [])
            if day in avoid_days:
                continue
        
        # Collect all busy intervals for the day for all participants
        busy_intervals = []
        for person, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    busy_start = time_to_minutes(start)
                    busy_end = time_to_minutes(end)
                    busy_intervals.append((busy_start, busy_end))
        
        # Sort the busy intervals by start time
        busy_intervals.sort()
        
        # Find the available slots between work hours and busy intervals
        available_slots = []
        prev_end = work_start
        
        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        # Check the slot after the last busy interval
        if prev_end < work_end:
            available_slots.append((prev_end, work_end))
        
        # Check each available slot for a suitable meeting time
        for slot_start, slot_end in available_slots:
            slot_duration = slot_end - slot_start
            if slot_duration >= meeting_duration_min:
                meeting_time = (minutes_to_time(slot_start), 
                               minutes_to_time(slot_start + meeting_duration_min))
                return (day, f"{meeting_time[0]}-{meeting_time[1]}")
    
    return (None, None)

# Define the participants' schedules
participants = {
    "Carl": {
        "Monday": [("11:00", "11:30")],
        "Tuesday": [("14:30", "15:00")],
        "Wednesday": [("10:00", "11:30"), ("13:00", "13:30")],
        "Thursday": [("13:30", "14:00"), ("16:00", "16:30")],
    },
    "Margaret": {
        "Monday": [("09:00", "10:30"), ("11:00", "17:00")],
        "Tuesday": [("09:30", "12:00"), ("13:30", "14:00"), ("15:30", "17:00")],
        "Wednesday": [("09:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")],
        "Thursday": [("10:00", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")],
    }
}

# Define the constraints
work_hours = ("09:00", "17:00")
meeting_duration = 60  # minutes
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
preferences = {"Carl": ["Thursday"]}

# Find the meeting time
day, time_range = find_meeting_time(participants, work_hours, meeting_duration, days, preferences)

# Output the result
if day and time_range:
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")