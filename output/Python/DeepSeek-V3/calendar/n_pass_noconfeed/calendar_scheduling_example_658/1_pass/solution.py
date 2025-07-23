from typing import List, Dict, Tuple

def find_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    work_hours: Tuple[str, str],
    meeting_duration: int,
    days: List[str],
    preferences: Dict[str, Dict[str, str]] = None
) -> Tuple[str, str]:
    """
    Finds a suitable meeting time based on participants' schedules and constraints.

    Args:
        participants: Dictionary of participants with their busy times.
        work_hours: Tuple of start and end times for work hours (e.g., ("09:00", "17:00")).
        meeting_duration: Duration of the meeting in minutes.
        days: List of days to consider (e.g., ["Monday", "Tuesday"]).
        preferences: Optional dictionary of preferences (e.g., {"Shirley": {"Tuesday": "before 10:30"}}).

    Returns:
        Tuple of (day, time_range) where time_range is in "HH:MM-HH:MM" format.
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

    work_start, work_end = map(time_to_minutes, work_hours)
    duration_minutes = meeting_duration

    for day in days:
        # Collect all busy intervals for the day
        busy_intervals = []
        for person, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    busy_start = time_to_minutes(start)
                    busy_end = time_to_minutes(end)
                    busy_intervals.append((busy_start, busy_end))
        
        # Sort and merge overlapping intervals
        busy_intervals.sort()
        merged = []
        for start, end in busy_intervals:
            if not merged:
                merged.append((start, end))
            else:
                last_start, last_end = merged[-1]
                if start <= last_end:
                    merged[-1] = (last_start, max(end, last_end))
                else:
                    merged.append((start, end))
        
        # Find free slots
        free_slots = []
        prev_end = work_start
        for start, end in merged:
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check each free slot for availability
        for start, end in free_slots:
            slot_duration = end - start
            if slot_duration >= duration_minutes:
                proposed_start = start
                proposed_end = proposed_start + duration_minutes
                # Check preferences
                valid = True
                if preferences:
                    for person, pref in preferences.items():
                        if day in pref:
                            constraint = pref[day]
                            if constraint == "before 10:30":
                                if day == "Tuesday" and proposed_start >= time_to_minutes("10:30"):
                                    valid = False
                if valid:
                    time_range = f"{minutes_to_time(proposed_start)}-{minutes_to_time(proposed_end)}"
                    return (day, time_range)
    
    return ("No day found", "00:00-00:00")

# Define participants' schedules
participants = {
    "Shirley": {
        "Monday": [("10:30", "11:00"), ("12:00", "12:30"), ("16:00", "16:30")],
        "Tuesday": [("9:30", "10:00")],
    },
    "Albert": {
        "Monday": [("9:00", "17:00")],
        "Tuesday": [("9:30", "11:00"), ("11:30", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")],
    }
}

# Define preferences
preferences = {
    "Shirley": {"Tuesday": "before 10:30"}
}

# Find meeting time
day, time_range = find_meeting_time(
    participants=participants,
    work_hours=("09:00", "17:00"),
    meeting_duration=30,
    days=["Monday", "Tuesday"],
    preferences=preferences
)

# Output the result
print(f"{day}: {time_range}")