from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since 9:00."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def find_earliest_meeting_time(
    participants: List[Dict[str, List[Tuple[int, int]]]],
    days: List[str],
    duration: int,
    work_start: str = "9:00",
    work_end: str = "17:00"
) -> Tuple[str, str]:
    """Find the earliest available meeting time for all participants.
    
    Args:
        participants: List of participants' busy schedules per day.
        days: List of days to consider (e.g., ["Monday", "Tuesday"]).
        duration: Meeting duration in minutes.
        work_start: Start of workday in HH:MM format.
        work_end: End of workday in HH:MM format.
    
    Returns:
        Tuple of (day, time_range) where time_range is "HH:MM-HH:MM".
    """
    work_start_min = parse_time(work_start)
    work_end_min = parse_time(work_end)
    
    for day_idx, day in enumerate(days):
        # Collect all busy intervals for the day across participants
        busy_intervals = []
        for participant in participants:
            if day in participant:
                busy_intervals.extend(participant[day])
        
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
        
        # Check available slots
        prev_end = work_start_min
        for start, end in merged:
            if start - prev_end >= duration:
                return (day, f"{format_time(prev_end)}-{format_time(prev_end + duration)}")
            prev_end = max(prev_end, end)
        
        # Check after last busy interval
        if work_end_min - prev_end >= duration:
            return (day, f"{format_time(prev_end)}-{format_time(prev_end + duration)}")
    
    return ("No day found", "")

# Define participants' schedules
nicole_schedule = {
    "Tuesday": [(parse_time("16:00"), parse_time("16:30"))],
    "Wednesday": [(parse_time("15:00"), parse_time("15:30"))],
    "Friday": [
        (parse_time("12:00"), parse_time("12:30")),
        (parse_time("15:30"), parse_time("16:00"))
    ]
}

daniel_schedule = {
    "Monday": [
        (parse_time("9:00"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("14:00"), parse_time("16:30"))
    ],
    "Tuesday": [
        (parse_time("9:00"), parse_time("10:30")),
        (parse_time("11:30"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("15:00"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ],
    "Wednesday": [
        (parse_time("9:00"), parse_time("10:00")),
        (parse_time("11:00"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("14:00"), parse_time("14:30")),
        (parse_time("16:30"), parse_time("17:00"))
    ],
    "Thursday": [
        (parse_time("11:00"), parse_time("12:00")),
        (parse_time("13:00"), parse_time("14:00")),
        (parse_time("15:00"), parse_time("15:30"))
    ],
    "Friday": [
        (parse_time("10:00"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("12:00")),
        (parse_time("12:30"), parse_time("14:30")),
        (parse_time("15:00"), parse_time("15:30")),
        (parse_time("16:00"), parse_time("16:30"))
    ]
}

participants = [nicole_schedule, daniel_schedule]
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
duration = 60  # 1 hour in minutes

day, time_range = find_earliest_meeting_time(participants, days, duration)
print(f"{day}: {time_range}")