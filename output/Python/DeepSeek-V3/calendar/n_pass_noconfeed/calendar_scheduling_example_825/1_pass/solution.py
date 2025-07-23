from typing import List, Dict, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in format HH:MM to minutes since 9:00."""
    hh, mm = map(int, time_str.split(':'))
    return (hh - 9) * 60 + mm

def format_time(minutes: int) -> str:
    """Convert minutes since 9:00 back to HH:MM format."""
    hh = 9 + minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def find_meeting_time(
    participants: List[Dict[str, List[Tuple[int, int]]]],
    days: List[str],
    duration: int,
    work_start: int = 0,  # 9:00 in minutes since 9:00
    work_end: int = 480,  # 17:00 in minutes since 9:00 (8 hours)
    excluded_days: List[str] = None
) -> Tuple[str, str]:
    """Find a meeting time that fits all participants' schedules."""
    if excluded_days is None:
        excluded_days = []
    
    for day_idx, day in enumerate(days):
        if day in excluded_days:
            continue
        
        # Merge all busy intervals for the day across participants
        busy_intervals = []
        for participant in participants:
            if day in participant:
                busy_intervals.extend(participant[day])
        
        # Sort and merge overlapping intervals
        if not busy_intervals:
            return day, f"{format_time(work_start)}:{format_time(work_start + duration)}"
        
        busy_intervals.sort()
        merged = [busy_intervals[0]]
        for current in busy_intervals[1:]:
            last = merged[-1]
            if current[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], current[1]))
            else:
                merged.append(current)
        
        # Check for available slots
        prev_end = work_start
        for start, end in merged:
            if start - prev_end >= duration:
                return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
            prev_end = max(prev_end, end)
        
        if work_end - prev_end >= duration:
            return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
    
    return None, None

# Define participants' schedules
laura_schedule = {
    "Monday": [
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("12:30"), parse_time("13:00")),
        (parse_time("14:30"), parse_time("15:30")),
        (parse_time("16:00"), parse_time("17:00")),
    ],
    "Tuesday": [
        (parse_time("09:30"), parse_time("10:00")),
        (parse_time("11:00"), parse_time("11:30")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("14:30"), parse_time("15:00")),
        (parse_time("16:00"), parse_time("17:00")),
    ],
    "Wednesday": [
        (parse_time("11:30"), parse_time("12:00")),
        (parse_time("12:30"), parse_time("13:00")),
        (parse_time("15:30"), parse_time("16:30")),
    ],
    "Thursday": [
        (parse_time("10:30"), parse_time("11:00")),
        (parse_time("12:00"), parse_time("13:30")),
        (parse_time("15:00"), parse_time("15:30")),
        (parse_time("16:00"), parse_time("16:30")),
    ],
}

philip_schedule = {
    "Monday": [
        (parse_time("09:00"), parse_time("17:00")),
    ],
    "Tuesday": [
        (parse_time("09:00"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("12:00")),
        (parse_time("13:00"), parse_time("13:30")),
        (parse_time("14:00"), parse_time("14:30")),
        (parse_time("15:00"), parse_time("16:30")),
    ],
    "Wednesday": [
        (parse_time("09:00"), parse_time("10:00")),
        (parse_time("11:00"), parse_time("12:00")),
        (parse_time("12:30"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00")),
    ],
    "Thursday": [
        (parse_time("09:00"), parse_time("10:30")),
        (parse_time("11:00"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("17:00")),
    ],
}

# Define parameters
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
duration = 60  # minutes
excluded_days = ["Wednesday"]

# Find meeting time
day, time_range = find_meeting_time(
    [laura_schedule, philip_schedule],
    days,
    duration,
    excluded_days=excluded_days
)

# Output result
print(f"{day}: {time_range}")