from typing import List, Dict, Tuple
import datetime

def parse_time(time_str: str) -> datetime.time:
    """Parse a time string in HH:MM format into a datetime.time object."""
    return datetime.datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time: datetime.time) -> int:
    """Convert a datetime.time object to total minutes since midnight."""
    return time.hour * 60 + time.minute

def minutes_to_time(minutes: int) -> datetime.time:
    """Convert total minutes since midnight to a datetime.time object."""
    return datetime.time(hour=minutes // 60, minute=minutes % 60)

def get_available_slots(busy_slots: List[Tuple[datetime.time, datetime.time]], 
                       work_start: datetime.time, 
                       work_end: datetime.time, 
                       duration: int) -> List[Tuple[datetime.time, datetime.time]]:
    """Calculate available time slots given busy slots, work hours, and meeting duration."""
    # Convert all times to minutes for easier calculation
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration
    
    # Sort busy slots by start time
    busy_slots_min = sorted([(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_slots])
    
    # Initialize available slots
    available_slots = []
    prev_end = work_start_min
    
    for start, end in busy_slots_min:
        if start > prev_end:
            # There's a gap between prev_end and start
            available_start = prev_end
            available_end = start
            if available_end - available_start >= duration_min:
                available_slots.append((available_start, available_end))
        prev_end = max(prev_end, end)
    
    # Check the slot after the last busy slot
    if work_end_min - prev_end >= duration_min:
        available_slots.append((prev_end, work_end_min))
    
    # Convert back to time objects
    return [(minutes_to_time(start), minutes_to_time(end)) for start, end in available_slots]

def find_common_slot(schedules: Dict[str, Dict[str, List[Tuple[datetime.time, datetime.time]]]], 
                     days: List[str], 
                     work_start: datetime.time, 
                     work_end: datetime.time, 
                     duration: int) -> Tuple[str, datetime.time, datetime.time]:
    """Find the first common available slot across all participants' schedules."""
    for day in days:
        # Collect all busy slots for the day for each participant
        all_busy_slots = []
        for person in schedules:
            all_busy_slots.extend(schedules[person].get(day, []))
        
        # Get available slots for the day considering all busy slots
        available_slots = get_available_slots(all_busy_slots, work_start, work_end, duration)
        
        if available_slots:
            # Return the first available slot
            start, end = available_slots[0]
            return day, start, end
    
    raise ValueError("No common slot found")

def main():
    # Define work hours and meeting duration
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    duration = 60  # minutes
    
    # Define days to consider
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    # Define schedules for each participant
    schedules = {
        "Natalie": {
            "Monday": [
                (parse_time("09:00"), parse_time("09:30")),
                (parse_time("10:00"), parse_time("12:00")),
                (parse_time("12:30"), parse_time("13:00")),
                (parse_time("14:00"), parse_time("14:30")),
                (parse_time("15:00"), parse_time("16:30"))
            ],
            "Tuesday": [
                (parse_time("09:00"), parse_time("09:30")),
                (parse_time("10:00"), parse_time("10:30")),
                (parse_time("12:30"), parse_time("14:00")),
                (parse_time("16:00"), parse_time("17:00"))
            ],
            "Wednesday": [
                (parse_time("11:00"), parse_time("11:30")),
                (parse_time("16:00"), parse_time("16:30"))
            ],
            "Thursday": [
                (parse_time("10:00"), parse_time("11:00")),
                (parse_time("11:30"), parse_time("15:00")),
                (parse_time("15:30"), parse_time("16:00")),
                (parse_time("16:30"), parse_time("17:00"))
            ]
        },
        "William": {
            "Monday": [
                (parse_time("09:30"), parse_time("11:00")),
                (parse_time("11:30"), parse_time("17:00"))
            ],
            "Tuesday": [
                (parse_time("09:00"), parse_time("13:00")),
                (parse_time("13:30"), parse_time("16:00"))
            ],
            "Wednesday": [
                (parse_time("09:00"), parse_time("12:30")),
                (parse_time("13:00"), parse_time("14:30")),
                (parse_time("15:30"), parse_time("16:00")),
                (parse_time("16:30"), parse_time("17:00"))
            ],
            "Thursday": [
                (parse_time("09:00"), parse_time("10:30")),
                (parse_time("11:00"), parse_time("11:30")),
                (parse_time("12:00"), parse_time("12:30")),
                (parse_time("13:00"), parse_time("14:00")),
                (parse_time("15:00"), parse_time("17:00"))
            ]
        }
    }
    
    # Find the first common available slot
    day, start, end = find_common_slot(schedules, days, work_start, work_end, duration)
    
    # Output the result
    print(f"{day}: {start.strftime('%H:%M')}:{end.strftime('%H:%M')}")

if __name__ == "__main__":
    main()