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
                       work_start: datetime.time, work_end: datetime.time, 
                       duration: int) -> List[Tuple[datetime.time, datetime.time]]:
    """Calculate available time slots given busy slots, work hours, and meeting duration."""
    # Convert all times to minutes for easier calculation
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration
    
    # Process busy slots: convert to minutes and sort
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
            if available_duration >= duration_min:
                available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check after last busy slot
    if work_end_min > prev_end:
        available_duration = work_end_min - prev_end
        if available_duration >= duration_min:
            available_slots.append((prev_end, work_end_min))
    
    # Convert back to time objects
    available_slots_time = []
    for start, end in available_slots:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(end)
        available_slots_time.append((start_time, end_time))
    
    return available_slots_time

def find_common_meeting_time(diane_schedule: Dict[str, List[Tuple[str, str]]], 
                            matthew_schedule: Dict[str, List[Tuple[str, str]]], 
                            work_hours: Tuple[str, str], 
                            duration: int, 
                            matthew_preferences: Dict[str, List[Tuple[str, str]]] = None) -> Tuple[str, str, str]:
    """Find a common meeting time for Diane and Matthew considering their schedules and preferences."""
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    
    for day in days:
        # Get busy slots for Diane and Matthew
        diane_busy = diane_schedule.get(day, [])
        matthew_busy = matthew_schedule.get(day, [])
        
        # Parse busy slots into time objects
        diane_busy_slots = [(parse_time(start), parse_time(end)) for start, end in diane_busy]
        matthew_busy_slots = [(parse_time(start), parse_time(end)) for start, end in matthew_busy]
        
        # Get available slots for Diane and Matthew
        diane_available = get_available_slots(diane_busy_slots, work_start, work_end, duration)
        matthew_available = get_available_slots(matthew_busy_slots, work_start, work_end, duration)
        
        # Find intersection of available slots
        common_slots = []
        for d_start, d_end in diane_available:
            for m_start, m_end in matthew_available:
                latest_start = max(d_start, m_start)
                earliest_end = min(d_end, m_end)
                if earliest_end > latest_start:
                    overlap_duration = (earliest_end.hour * 60 + earliest_end.minute) - (latest_start.hour * 60 + latest_start.minute)
                    if overlap_duration >= duration:
                        common_slots.append((latest_start, earliest_end))
        
        # Apply Matthew's preferences if any
        if matthew_preferences and day in matthew_preferences:
            preferred_times = [(parse_time(start), parse_time(end)) for start, end in matthew_preferences[day]]
            preferred_slots = []
            for start, end in common_slots:
                for p_start, p_end in preferred_times:
                    latest_start = max(start, p_start)
                    earliest_end = min(end, p_end)
                    if earliest_end > latest_start:
                        preferred_slots.append((latest_start, earliest_end))
            common_slots = preferred_slots
        
        if common_slots:
            # Return the first available slot
            start_time = common_slots[0][0].strftime("%H:%M")
            end_time = common_slots[0][1].strftime("%H:%M")
            return day, start_time, end_time
    
    return None, None, None

# Define schedules
diane_schedule = {
    "Monday": [("12:00", "12:30"), ("15:00", "15:30")],
    "Tuesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("16:00", "17:00")],
    "Wednesday": [("9:00", "9:30"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Thursday": [("15:30", "16:30")],
    "Friday": [("9:30", "11:30"), ("14:30", "15:00"), ("16:00", "17:00")]
}

matthew_schedule = {
    "Monday": [("9:00", "10:00"), ("10:30", "17:00")],
    "Tuesday": [("9:00", "17:00")],
    "Wednesday": [("9:00", "11:00"), ("12:00", "14:30"), ("16:00", "17:00")],
    "Thursday": [("9:00", "16:00")],
    "Friday": [("9:00", "17:00")]
}

# Matthew's preference: not Wednesday before 12:30
matthew_preferences = {
    "Wednesday": [("12:30", "17:00")]
}

# Find meeting time
day, start_time, end_time = find_common_meeting_time(
    diane_schedule, 
    matthew_schedule, 
    ("9:00", "17:00"), 
    60,
    matthew_preferences
)

# Output the result
if day:
    print(f"{day}: {start_time} - {end_time}")
else:
    print("No suitable meeting time found.")