from typing import List, Dict, Tuple
import datetime

def parse_time(time_str: str) -> datetime.time:
    """Parse a time string in HH:MM format into a datetime.time object."""
    hours, minutes = map(int, time_str.split(':'))
    return datetime.time(hours, minutes)

def time_to_minutes(time: datetime.time) -> int:
    """Convert a datetime.time object to total minutes since midnight."""
    return time.hour * 60 + time.minute

def minutes_to_time(minutes: int) -> datetime.time:
    """Convert total minutes since midnight to a datetime.time object."""
    hours = minutes // 60
    minutes = minutes % 60
    return datetime.time(hours, minutes)

def get_available_slots(busy_slots: List[Tuple[datetime.time, datetime.time]], 
                        work_start: datetime.time, work_end: datetime.time, 
                        duration: int) -> List[Tuple[datetime.time, datetime.time]]:
    """Calculate available time slots given busy slots, work hours, and meeting duration."""
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Convert busy slots to minutes and sort them
    busy_minutes = []
    for start, end in busy_slots:
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        busy_minutes.append((start_min, end_min))
    busy_minutes.sort()
    
    # Find available slots
    available_slots = []
    prev_end = work_start_min
    
    for start, end in busy_minutes:
        if start > prev_end:
            available_duration = start - prev_end
            if available_duration >= duration:
                available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check after last busy slot
    if work_end_min - prev_end >= duration:
        available_slots.append((prev_end, work_end_min))
    
    # Convert back to time objects
    available_time_slots = []
    for start, end in available_slots:
        available_time_slots.append((minutes_to_time(start), minutes_to_time(end)))
    
    return available_time_slots

def find_common_slot(brian_slots: Dict[str, List[Tuple[datetime.time, datetime.time]]], 
                     julia_slots: Dict[str, List[Tuple[datetime.time, datetime.time]]], 
                     work_start: datetime.time, work_end: datetime.time, 
                     duration: int, avoid_day: str = None) -> Tuple[str, datetime.time, datetime.time]:
    """Find the earliest common available slot between Brian and Julia, avoiding specified day if possible."""
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    
    # Try to avoid the specified day by checking other days first
    if avoid_day:
        days.remove(avoid_day)
        days.insert(0, avoid_day)  # Check avoid_day last
    
    for day in days:
        # Get available slots for Brian and Julia on this day
        brian_available = get_available_slots(brian_slots.get(day, []), work_start, work_end, duration)
        julia_available = get_available_slots(julia_slots.get(day, []), work_start, work_end, duration)
        
        # Find the earliest common slot
        for b_start, b_end in brian_available:
            for j_start, j_end in julia_available:
                # Find overlap
                overlap_start = max(b_start, j_start)
                overlap_end = min(b_end, j_end)
                if time_to_minutes(overlap_end) - time_to_minutes(overlap_start) >= duration:
                    return day, overlap_start, minutes_to_time(time_to_minutes(overlap_start) + duration)
    
    return None, None, None

def main():
    # Define work hours and meeting duration
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    duration = 60  # minutes
    
    # Define busy slots for Brian and Julia
    brian_busy = {
        "Monday": [
            (parse_time("09:30"), parse_time("10:00")),
            (parse_time("12:30"), parse_time("14:30")),
            (parse_time("15:30"), parse_time("16:00"))
        ],
        "Tuesday": [
            (parse_time("09:00"), parse_time("09:30"))
        ],
        "Wednesday": [
            (parse_time("12:30"), parse_time("14:00")),
            (parse_time("16:30"), parse_time("17:00"))
        ],
        "Thursday": [
            (parse_time("11:00"), parse_time("11:30")),
            (parse_time("13:00"), parse_time("13:30")),
            (parse_time("16:30"), parse_time("17:00"))
        ],
        "Friday": [
            (parse_time("09:30"), parse_time("10:00")),
            (parse_time("10:30"), parse_time("11:00")),
            (parse_time("13:00"), parse_time("13:30")),
            (parse_time("15:00"), parse_time("16:00")),
            (parse_time("16:30"), parse_time("17:00"))
        ]
    }
    
    julia_busy = {
        "Monday": [
            (parse_time("09:00"), parse_time("10:00")),
            (parse_time("11:00"), parse_time("11:30")),
            (parse_time("12:30"), parse_time("13:00")),
            (parse_time("15:30"), parse_time("16:00"))
        ],
        "Tuesday": [
            (parse_time("13:00"), parse_time("14:00")),
            (parse_time("16:00"), parse_time("16:30"))
        ],
        "Wednesday": [
            (parse_time("09:00"), parse_time("11:30")),
            (parse_time("12:00"), parse_time("12:30")),
            (parse_time("13:00"), parse_time("17:00"))
        ],
        "Thursday": [
            (parse_time("09:00"), parse_time("10:30")),
            (parse_time("11:00"), parse_time("17:00"))
        ],
        "Friday": [
            (parse_time("09:00"), parse_time("10:00")),
            (parse_time("10:30"), parse_time("11:30")),
            (parse_time("12:30"), parse_time("14:00")),
            (parse_time("14:30"), parse_time("15:00")),
            (parse_time("15:30"), parse_time("16:00"))
        ]
    }
    
    # Find the earliest common slot, avoiding Monday if possible
    day, start_time, end_time = find_common_slot(brian_busy, julia_busy, work_start, work_end, duration, "Monday")
    
    if day:
        # Format the output
        start_str = start_time.strftime("%H:%M")
        end_str = end_time.strftime("%H:%M")
        print(f"{day}: {start_str}:{end_str}")
    else:
        print("No suitable time slot found.")

if __name__ == "__main__":
    main()