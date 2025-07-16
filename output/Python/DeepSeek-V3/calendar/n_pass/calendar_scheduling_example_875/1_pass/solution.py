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

def find_available_slot(
    schedules: Dict[str, List[Tuple[int, int]]],
    duration: int,
    days: List[str],
    work_start: str = "9:00",
    work_end: str = "17:00"
) -> Tuple[str, str]:
    """Find the first available meeting slot that fits all participants' schedules.
    
    Args:
        schedules: Dictionary where keys are participant names and values are lists of busy intervals (in HH:MM format).
        duration: Meeting duration in minutes.
        days: List of days to consider (e.g., ["Monday", "Tuesday"]).
        work_start: Start of workday in HH:MM format.
        work_end: End of workday in HH:MM format.
    
    Returns:
        Tuple of (day, time_range) where time_range is in "HH:MM-HH:MM" format.
    """
    work_start_min = parse_time(work_start)
    work_end_min = parse_time(work_end)
    
    for day in days:
        # Collect all busy intervals for the day
        all_busy = []
        for participant in schedules.values():
            all_busy.extend(participant.get(day, []))
        
        # Merge overlapping or adjacent busy intervals
        if not all_busy:
            # No busy intervals, entire day is free
            return (day, f"{work_start}-{format_time(parse_time(work_start) + duration)}")
        
        # Sort intervals by start time
        all_busy.sort()
        merged = [all_busy[0]]
        for current in all_busy[1:]:
            last = merged[-1]
            if current[0] <= last[1]:
                # Overlapping or adjacent, merge them
                merged[-1] = (last[0], max(last[1], current[1]))
            else:
                merged.append(current)
        
        # Check for available slots between busy intervals
        prev_end = work_start_min
        for busy_start, busy_end in merged:
            if busy_start - prev_end >= duration:
                # Found a slot
                start_time = format_time(prev_end)
                end_time = format_time(prev_end + duration)
                return (day, f"{start_time}-{end_time}")
            prev_end = max(prev_end, busy_end)
        
        # Check after last busy interval
        if work_end_min - prev_end >= duration:
            start_time = format_time(prev_end)
            end_time = format_time(prev_end + duration)
            return (day, f"{start_time}-{end_time}")
    
    raise ValueError("No available slot found")

def main():
    # Define schedules for each participant
    natalie_schedule = {
        "Monday": [("9:00", "9:30"), ("10:00", "12:00"), ("12:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("12:30", "14:00"), ("16:00", "17:00")],
        "Wednesday": [("11:00", "11:30"), ("16:00", "16:30")],
        "Thursday": [("10:00", "11:00"), ("11:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    }
    
    william_schedule = {
        "Monday": [("9:30", "11:00"), ("11:30", "17:00")],
        "Tuesday": [("9:00", "13:00"), ("13:30", "16:00")],
        "Wednesday": [("9:00", "12:30"), ("13:00", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("9:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("15:00", "17:00")],
    }
    
    # Convert schedules to minutes since 9:00 for easier processing
    def convert_schedule(schedule):
        converted = {}
        for day, intervals in schedule.items():
            converted[day] = [(parse_time(start), parse_time(end)) for start, end in intervals]
        return converted
    
    natalie_converted = convert_schedule(natalie_schedule)
    william_converted = convert_schedule(william_schedule)
    
    schedules = {
        "Natalie": natalie_converted,
        "William": william_converted,
    }
    
    # Find available slot
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    duration = 60  # 1 hour
    
    day, time_range = find_available_slot(schedules, duration, days)
    print(f"{day}: {time_range}")

if __name__ == "__main__":
    main()