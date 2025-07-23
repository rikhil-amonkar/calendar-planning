from typing import List, Dict, Tuple

def find_meeting_time(
    participants: List[str],
    schedules: Dict[str, List[Tuple[str, str]]],
    work_hours: Tuple[str, str],
    duration_minutes: int,
    preferences: Dict[str, List[Tuple[str, str]]] = None
) -> Tuple[str, str]:
    """
    Finds a meeting time that works for all participants based on their schedules and preferences.
    
    Args:
        participants: List of participant names.
        schedules: Dictionary mapping participant names to their busy time slots (as tuples of "HH:MM" strings).
        work_hours: Tuple of start and end times of work hours (as "HH:MM" strings).
        duration_minutes: Duration of the meeting in minutes.
        preferences: Optional dictionary mapping participant names to time ranges they'd like to avoid.
    
    Returns:
        Tuple of (day, time_range) where time_range is "HH:MM-HH:MM".
    """
    def time_to_minutes(time_str: str) -> int:
        """Converts time string (HH:MM) to minutes since midnight."""
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes: int) -> str:
        """Converts minutes since midnight to time string (HH:MM)."""
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration = duration_minutes
    
    # Collect all busy intervals for all participants
    all_busy = []
    for participant in participants:
        for start, end in schedules.get(participant, []):
            all_busy.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Collect all preference-avoid intervals
    avoid_intervals = []
    if preferences:
        for participant, pref_slots in preferences.items():
            if participant in participants:
                for start, end in pref_slots:
                    avoid_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Combine all busy and avoid intervals
    all_intervals = all_busy + avoid_intervals
    all_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for start, end in all_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(end, last_end)
            else:
                merged.append([start, end])
    
    # Find available slots
    available = []
    prev_end = work_start_min
    for start, end in merged:
        if start > prev_end:
            available.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end_min:
        available.append((prev_end, work_end_min))
    
    # Find the first available slot that fits the duration
    for start, end in available:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return ("Monday", f"{minutes_to_time(meeting_start)}-{minutes_to_time(meeting_end)}")
    
    return (None, None)

# Define participants
participants = ["Katherine", "Rebecca", "Julie", "Angela", "Nicholas", "Carl"]

# Define schedules (busy times)
schedules = {
    "Katherine": [("12:00", "12:30"), ("13:00", "14:30")],
    "Julie": [("09:00", "09:30"), ("10:30", "11:00"), ("13:30", "14:00"), ("15:00", "15:30")],
    "Angela": [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "14:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Nicholas": [("09:30", "11:00"), ("11:30", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
    "Carl": [("09:00", "11:00"), ("11:30", "12:30"), ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
}

# Define work hours
work_hours = ("09:00", "17:00")

# Define duration (30 minutes)
duration = 30

# Define Angela's preference to avoid meetings before 15:00
preferences = {
    "Angela": [("09:00", "15:00")]
}

# Find meeting time
day, time_range = find_meeting_time(participants, schedules, work_hours, duration, preferences)

# Output the result
print(f"{day}: {time_range}")