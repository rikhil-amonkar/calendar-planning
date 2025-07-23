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
    
    # Sort busy slots by start time
    busy_slots_min.sort()
    
    available_slots = []
    prev_end = work_start_min
    
    for start, end in busy_slots_min:
        if start > prev_end:
            available_duration = start - prev_end
            if available_duration >= duration:
                available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check after last busy slot
    if work_end_min - prev_end >= duration:
        available_slots.append((prev_end, work_end_min))
    
    # Convert back to time objects
    return [(minutes_to_time(start), minutes_to_time(end)) for start, end in available_slots]

def find_earliest_meeting_time(schedules: Dict[str, Dict[str, List[Tuple[str, str]]]], 
                              participants: List[str], 
                              days: List[str], 
                              duration: int, 
                              work_start: str, 
                              work_end: str, 
                              preferences: Dict[str, List[str]] = None) -> Tuple[str, Tuple[datetime.time, datetime.time]]:
    """Find the earliest available meeting time that fits all participants' schedules."""
    work_start_time = parse_time(work_start)
    work_end_time = parse_time(work_end)
    
    for day in days:
        if preferences and day in preferences.get("avoid_days", []):
            continue
        
        # Collect all busy slots for the day for all participants
        all_busy_slots = []
        for participant in participants:
            participant_schedule = schedules.get(participant, {}).get(day, [])
            participant_busy_slots = [(parse_time(start), parse_time(end)) for start, end in participant_schedule]
            all_busy_slots.extend(participant_busy_slots)
        
        # Merge overlapping busy slots
        if not all_busy_slots:
            # No busy slots, the whole day is available
            return day, (work_start_time, minutes_to_time(time_to_minutes(work_start_time) + duration))
        
        # Sort and merge busy slots
        all_busy_slots.sort()
        merged_busy = [all_busy_slots[0]]
        for current_start, current_end in all_busy_slots[1:]:
            last_start, last_end = merged_busy[-1]
            if current_start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, current_start)
                new_end = max(last_end, current_end)
                merged_busy[-1] = (new_start, new_end)
            else:
                merged_busy.append((current_start, current_end))
        
        # Get available slots
        available_slots = get_available_slots(merged_busy, work_start_time, work_end_time, duration)
        if available_slots:
            earliest_slot = available_slots[0]
            return day, earliest_slot
    
    return None, None

# Define the schedules
schedules = {
    "Robert": {
        "Monday": [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
        "Tuesday": [("10:30", "11:00"), ("15:00", "15:30")],
        "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
    "Ralph": {
        "Monday": [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
        "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"), ("16:30", "17:00")],
    }
}

# Define preferences
preferences = {
    "Robert": {
        "avoid_days": ["Monday"]
    }
}

# Find the earliest meeting time
day, slot = find_earliest_meeting_time(
    schedules=schedules,
    participants=["Robert", "Ralph"],
    days=["Tuesday", "Wednesday", "Monday"],  # Ordered by preference (Monday last due to avoidance)
    duration=30,
    work_start="9:00",
    work_end="17:00",
    preferences=preferences
)

# Output the result
if day and slot:
    start_time, end_time = slot
    print(f"{day}:{start_time.hour:02d}:{start_time.minute:02d}:{end_time.hour:02d}:{end_time.minute:02d}")
else:
    print("No suitable time found.")