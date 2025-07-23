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
                       duration_minutes: int) -> List[Tuple[datetime.time, datetime.time]]:
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
            available_start = prev_end
            available_end = start
            if available_end - available_start >= duration_minutes:
                available_slots.append((available_start, available_end))
        prev_end = max(prev_end, end)
    
    if work_end_min > prev_end:
        available_start = prev_end
        available_end = work_end_min
        if available_end - available_start >= duration_minutes:
            available_slots.append((available_start, available_end))
    
    # Convert back to time objects
    available_time_slots = []
    for start_min, end_min in available_slots:
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        available_time_slots.append((start_time, end_time))
    
    return available_time_slots

def find_meeting_time(participants: Dict[str, Dict[str, List[Tuple[str, str]]]], 
                      days: List[str], work_hours: Tuple[str, str], 
                      duration: int, preferences: Dict[str, List[str]] = None) -> Tuple[str, str]:
    """Find a meeting time that works for all participants."""
    work_start = parse_time(work_hours[0])
    work_end = parse_time(work_hours[1])
    duration_minutes = duration
    
    for day in days:
        if preferences and day in preferences.get('avoid_days', []):
            continue
        
        # Collect all busy slots for the day
        all_busy_slots = []
        for person, schedule in participants.items():
            busy_slots = schedule.get(day, [])
            for start, end in busy_slots:
                all_busy_slots.append((parse_time(start), parse_time(end)))
        
        # Get available slots for the day
        available_slots = get_available_slots(all_busy_slots, work_start, work_end, duration_minutes)
        
        if available_slots:
            # Pick the first available slot
            start_time, end_time = available_slots[0]
            meeting_end_min = time_to_minutes(start_time) + duration_minutes
            meeting_end_time = minutes_to_time(meeting_end_min)
            return day, f"{start_time.hour:02d}:{start_time.minute:02d}:{meeting_end_time.hour:02d}:{meeting_end_time.minute:02d}"
    
    return None, None

# Define participants' schedules
participants = {
    "Eugene": {
        "Monday": [("11:00", "12:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("16:00", "16:30")],
        "Wednesday": [("9:00", "9:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "15:00")],
        "Thursday": [("9:30", "10:00"), ("11:00", "12:30")],
        "Friday": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30")]
    },
    "Eric": {
        "Monday": [("9:00", "17:00")],
        "Tuesday": [("9:00", "17:00")],
        "Wednesday": [("9:00", "11:30"), ("12:00", "14:00"), ("14:30", "16:30")],
        "Thursday": [("9:00", "17:00")],
        "Friday": [("9:00", "11:00"), ("11:30", "17:00")]
    }
}

# Define meeting constraints
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
work_hours = ("9:00", "17:00")
duration = 30  # minutes
preferences = {"Eric": {"avoid_days": ["Wednesday"]}}

# Find meeting time
day, time_range = find_meeting_time(participants, days, work_hours, duration, preferences)

# Output the result
print(f"{day}, {time_range}")