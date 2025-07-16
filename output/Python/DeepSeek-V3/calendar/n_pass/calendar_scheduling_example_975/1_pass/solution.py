from typing import Dict, List, Tuple

def parse_time(time_str: str) -> int:
    """Convert time string in HH:MM format to minutes since midnight."""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes: int) -> str:
    """Convert minutes since midnight to HH:MM format."""
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def find_earliest_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[int, int]]]],
    days: List[str],
    work_hours: Tuple[str, str],
    duration: int
) -> Tuple[str, str]:
    """Find the earliest available meeting time for all participants."""
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    for day in days:
        # Collect all busy intervals for the day for all participants
        busy_intervals = []
        for person, schedule in participants.items():
            if day in schedule:
                busy_intervals.extend(schedule[day])
        
        # Merge overlapping or adjacent intervals
        if not busy_intervals:
            # No busy intervals, entire work day is free
            return day, f"{format_time(work_start)}:{format_time(work_start + duration)}"
        
        # Sort intervals by start time
        busy_intervals.sort()
        
        # Check the time before the first busy interval
        first_start = busy_intervals[0][0]
        if first_start - work_start >= duration:
            return day, f"{format_time(work_start)}:{format_time(work_start + duration)}"
        
        # Check gaps between busy intervals
        prev_end = busy_intervals[0][1]
        for start, end in busy_intervals[1:]:
            if start - prev_end >= duration:
                return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
            prev_end = max(prev_end, end)
        
        # Check the time after the last busy interval
        if work_end - prev_end >= duration:
            return day, f"{format_time(prev_end)}:{format_time(prev_end + duration)}"
    
    raise ValueError("No suitable meeting time found.")

def main():
    # Define participants' schedules
    participants = {
        "Nicole": {
            "Tuesday": [(parse_time("16:00"), parse_time("16:30"))],
            "Wednesday": [(parse_time("15:00"), parse_time("15:30"))],
            "Friday": [
                (parse_time("12:00"), parse_time("12:30")),
                (parse_time("15:30"), parse_time("16:00"))
            ],
        },
        "Daniel": {
            "Monday": [
                (parse_time("09:00"), parse_time("12:30")),
                (parse_time("13:00"), parse_time("13:30")),
                (parse_time("14:00"), parse_time("16:30"))
            ],
            "Tuesday": [
                (parse_time("09:00"), parse_time("10:30")),
                (parse_time("11:30"), parse_time("12:30")),
                (parse_time("13:00"), parse_time("13:30")),
                (parse_time("15:00"), parse_time("16:00")),
                (parse_time("16:30"), parse_time("17:00"))
            ],
            "Wednesday": [
                (parse_time("09:00"), parse_time("10:00")),
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
            ],
        },
    }
    
    # Define meeting constraints
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_hours = ("09:00", "17:00")
    duration = 60  # minutes
    
    day, time_range = find_earliest_meeting_time(participants, days, work_hours, duration)
    print(f"{day}: {time_range}")

if __name__ == "__main__":
    main()