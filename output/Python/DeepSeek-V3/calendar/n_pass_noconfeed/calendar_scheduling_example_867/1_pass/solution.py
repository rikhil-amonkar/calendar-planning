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

def is_available(person_busy: List[Tuple[datetime.time, datetime.time]], start: datetime.time, end: datetime.time) -> bool:
    """Check if a person is available during the given time slot."""
    start_min = time_to_minutes(start)
    end_min = time_to_minutes(end)
    for busy_start, busy_end in person_busy:
        busy_start_min = time_to_minutes(busy_start)
        busy_end_min = time_to_minutes(busy_end)
        if not (end_min <= busy_start_min or start_min >= busy_end_min):
            return False
    return True

def find_meeting_time(
    betty_busy: Dict[str, List[Tuple[str, str]]],
    scott_busy: Dict[str, List[Tuple[str, str]]],
    duration: int,
    work_hours: Tuple[str, str],
    days: List[str],
    betty_constraints: Dict[str, List[str]],
    scott_preferences: List[str]
) -> Tuple[str, str]:
    """Find a suitable meeting time based on constraints and preferences."""
    work_start, work_end = parse_time(work_hours[0]), parse_time(work_hours[1])
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Convert busy times to datetime.time objects
    betty_busy_times = {}
    for day, slots in betty_busy.items():
        betty_busy_times[day] = [(parse_time(start), parse_time(end)) for start, end in slots]
    
    scott_busy_times = {}
    for day, slots in scott_busy.items():
        scott_busy_times[day] = [(parse_time(start), parse_time(end)) for start, end in slots]
    
    # Filter days based on Betty's constraints and Scott's preferences
    possible_days = []
    for day in days:
        if day in betty_constraints.get("cannot_meet", []):
            continue
        if day in scott_preferences.get("avoid_days", []):
            continue
        possible_days.append(day)
    
    # Check each possible day for available slots
    for day in possible_days:
        day_betty_busy = betty_busy_times.get(day, [])
        day_scott_busy = scott_busy_times.get(day, [])
        
        # Apply Betty's time constraints
        if day in betty_constraints.get("before_time", {}):
            constraint_time = parse_time(betty_constraints["before_time"][day])
            constraint_min = time_to_minutes(constraint_time)
        else:
            constraint_min = work_start_min
        
        current_start = max(work_start_min, constraint_min)
        
        while current_start + duration <= work_end_min:
            start_time = minutes_to_time(current_start)
            end_time = minutes_to_time(current_start + duration)
            
            # Check Betty's availability
            betty_ok = is_available(day_betty_busy, start_time, end_time)
            
            # Check Scott's availability
            scott_ok = is_available(day_scott_busy, start_time, end_time)
            
            if betty_ok and scott_ok:
                return day, f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}"
            
            current_start += 15  # Check in 15-minute increments
    
    return None, None

def main():
    # Define the problem constraints
    betty_busy = {
        "Monday": [("10:00", "10:30"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
        "Wednesday": [("9:30", "10:30"), ("13:00", "13:30"), ("14:00", "14:30")],
        "Thursday": [("9:30", "10:00"), ("11:30", "12:00"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:30", "17:00")]
    }
    
    scott_busy = {
        "Monday": [("9:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],
        "Wednesday": [("9:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Thursday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
    
    duration = 30  # minutes
    work_hours = ("9:00", "17:00")
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    
    betty_constraints = {
        "cannot_meet": ["Monday"],
        "before_time": {
            "Tuesday": "15:00",
            "Thursday": "15:00"
        }
    }
    
    scott_preferences = {
        "avoid_days": ["Wednesday"]
    }
    
    day, time_range = find_meeting_time(
        betty_busy,
        scott_busy,
        duration,
        work_hours,
        days,
        betty_constraints,
        scott_preferences
    )
    
    if day and time_range:
        print(f"{day}: {time_range}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()