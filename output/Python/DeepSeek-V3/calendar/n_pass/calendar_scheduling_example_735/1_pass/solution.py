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

def find_earliest_meeting_slot(
    participants: List[Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    duration: int,
    work_hours: Tuple[str, str]
) -> Tuple[str, str]:
    """Find the earliest available meeting slot for all participants."""
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    for day in days:
        # Collect all busy intervals for the day
        busy_intervals = []
        for participant in participants:
            if day in participant:
                for start, end in participant[day]:
                    busy_intervals.append((parse_time(start), parse_time(end)))
        
        # Sort and merge overlapping intervals
        if not busy_intervals:
            return day, f"{work_hours[0]}:{format_time(parse_time(work_hours[0]) + duration)}"
        
        busy_intervals.sort()
        merged = [busy_intervals[0]]
        for current in busy_intervals[1:]:
            last = merged[-1]
            if current[0] <= last[1]:
                merged[-1] = (last[0], max(last[1], current[1]))
            else:
                merged.append(current)
        
        # Check available slots
        prev_end = work_start
        for start, end in merged:
            if start - prev_end >= duration:
                return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
            prev_end = max(prev_end, end)
        
        if work_end - prev_end >= duration:
            return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
    
    return None, None

# Define participants' schedules
ronald_schedule = {
    "Monday": [("10:30", "11:00"), ("12:00", "12:30"), ("15:30", "16:00")],
    "Tuesday": [("9:00", "9:30"), ("12:00", "12:30"), ("15:30", "16:30")],
    "Wednesday": [("9:30", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
}

amber_schedule = {
    "Monday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:30", "12:00"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Tuesday": [("9:00", "9:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:30"), ("16:30", "17:00")],
    "Wednesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "13:30"), ("15:00", "15:30")],
}

participants = [ronald_schedule, amber_schedule]
days = ["Monday", "Tuesday", "Wednesday"]
duration = 30  # minutes
work_hours = ("9:00", "17:00")

day, time_slot = find_earliest_meeting_slot(participants, days, duration, work_hours)
print(f"{day}: {time_slot}")