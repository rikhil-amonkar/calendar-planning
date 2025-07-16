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
    busy_slots_min = [(time_to_minutes(start), time_to_minutes(end)) for start, end in busy_slots]
    
    # Initialize available slots
    available_slots = []
    
    # Sort busy slots by start time
    busy_slots_min.sort()
    
    # Check before first busy slot
    first_busy_start = busy_slots_min[0][0] if busy_slots_min else work_end_min
    if first_busy_start - work_start_min >= duration:
        available_slots.append((work_start_min, first_busy_start))
    
    # Check between busy slots
    for i in range(1, len(busy_slots_min)):
        prev_end = busy_slots_min[i-1][1]
        curr_start = busy_slots_min[i][0]
        if curr_start - prev_end >= duration:
            available_slots.append((prev_end, curr_start))
    
    # Check after last busy slot
    if busy_slots_min:
        last_busy_end = busy_slots_min[-1][1]
        if work_end_min - last_busy_end >= duration:
            available_slots.append((last_busy_end, work_end_min))
    else:
        if work_end_min - work_start_min >= duration:
            available_slots.append((work_start_min, work_end_min))
    
    # Convert back to time objects
    return [(minutes_to_time(start), minutes_to_time(end)) for start, end in available_slots]

def find_meeting_time(eugene_busy: Dict[str, List[Tuple[str, str]]], 
                      eric_busy: Dict[str, List[Tuple[str, str]]], 
                      days: List[str], 
                      work_start: str, 
                      work_end: str, 
                      duration: int,
                      eric_preferred_days: List[str] = None) -> Tuple[str, Tuple[datetime.time, datetime.time]]:
    """Find a meeting time that works for both Eugene and Eric, considering their busy slots and preferences."""
    work_start_time = parse_time(work_start)
    work_end_time = parse_time(work_end)
    
    # Convert busy slots to datetime.time objects
    eugene_busy_converted = {}
    for day, slots in eugene_busy.items():
        eugene_day_slots = [(parse_time(start), parse_time(end)) for start, end in slots]
        eugene_busy_converted[day] = eugene_day_slots
    
    eric_busy_converted = {}
    for day, slots in eric_busy.items():
        eric_day_slots = [(parse_time(start), parse_time(end)) for start, end in slots]
        eric_busy_converted[day] = eric_day_slots
    
    # Check each day in order, prioritizing non-preferred days first if specified
    if eric_preferred_days:
        days_to_check = [day for day in days if day not in eric_preferred_days] + \
                       [day for day in days if day in eric_preferred_days]
    else:
        days_to_check = days
    
    for day in days_to_check:
        # Get Eugene's available slots
        eugene_busy_slots = eugene_busy_converted.get(day, [])
        eugene_available = get_available_slots(eugene_busy_slots, work_start_time, work_end_time, duration)
        
        # Get Eric's available slots
        eric_busy_slots = eric_busy_converted.get(day, [])
        eric_available = get_available_slots(eric_busy_slots, work_start_time, work_end_time, duration)
        
        # Find overlapping slots
        for eugene_slot in eugene_available:
            for eric_slot in eric_available:
                # Check if slots overlap
                overlap_start = max(time_to_minutes(eugene_slot[0]), time_to_minutes(eric_slot[0]))
                overlap_end = min(time_to_minutes(eugene_slot[1]), time_to_minutes(eric_slot[1]))
                
                if overlap_end - overlap_start >= duration:
                    meeting_start = minutes_to_time(overlap_start)
                    meeting_end = minutes_to_time(overlap_start + duration)
                    return day, (meeting_start, meeting_end)
    
    raise ValueError("No suitable meeting time found.")

# Define the input data
eugene_busy = {
    "Monday": [("11:00", "12:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Wednesday": [("9:00", "9:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:00")],
    "Thursday": [("9:30", "10:00"), ("11:00", "12:30")],
    "Friday": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30")],
}

eric_busy = {
    "Monday": [("9:00", "17:00")],
    "Tuesday": [("9:00", "17:00")],
    "Wednesday": [("9:00", "11:30"), ("12:00", "14:00"), ("14:30", "16:30")],
    "Thursday": [("9:00", "17:00")],
    "Friday": [("9:00", "11:00"), ("11:30", "17:00")],
}

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
work_start = "9:00"
work_end = "17:00"
duration = 30  # minutes
eric_preferred_days = ["Wednesday"]  # Days to avoid (since Eric wants to avoid more meetings on Wednesday)

# Find the meeting time
try:
    day, (start_time, end_time) = find_meeting_time(
        eugene_busy, eric_busy, days, work_start, work_end, duration, eric_preferred_days
    )
    # Format the output as HH:MM:HH:MM and day of the week
    print(f"{day}, {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
except ValueError as e:
    print(e)