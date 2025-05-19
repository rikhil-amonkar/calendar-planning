from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return datetime.strptime(f"{hours:02d}:{mins:02d}", "%H:%M").time()

def is_available(person_busy, day, start_time, end_time):
    for busy_block in person_busy.get(day, []):
        busy_start = time_to_minutes(parse_time(busy_block[0]))
        busy_end = time_to_minutes(parse_time(busy_block[1]))
        if not (end_time <= busy_start or start_time >= busy_end):
            return False
    return True

def find_meeting_time(daniel_busy, bradley_busy, preferences, duration_minutes):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = time_to_minutes(parse_time("9:00"))
    work_end = time_to_minutes(parse_time("17:00"))
    
    for day in days:
        # Check preferences
        if day in preferences.get("Daniel", {}).get("avoid_days", []):
            continue
        if day in preferences.get("Bradley", {}).get("avoid_days", []):
            continue
        
        current_time = work_start
        while current_time + duration_minutes <= work_end:
            start_time = current_time
            end_time = current_time + duration_minutes
            
            # Check Bradley's before 12:00 preference on Tuesday
            if day == "Tuesday" and end_time <= time_to_minutes(parse_time("12:00")):
                if preferences.get("Bradley", {}).get("avoid_tuesday_before_12", False):
                    current_time += 15  # Skip in 15-minute increments
                    continue
            
            # Check both persons' availability
            daniel_available = is_available(daniel_busy, day, start_time, end_time)
            bradley_available = is_available(bradley_busy, day, start_time, end_time)
            
            if daniel_available and bradley_available:
                start_str = minutes_to_time(start_time).strftime("%H:%M")
                end_str = minutes_to_time(end_time).strftime("%H:%M")
                return day, f"{start_str}:{end_str}"
            
            current_time += 15  # Check in 15-minute increments
    
    return None, None

# Define busy schedules
daniel_busy = {
    "Monday": [("9:30", "10:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Tuesday": [("11:00", "12:00"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Wednesday": [("9:00", "10:00"), ("14:00", "14:30")],
    "Thursday": [("10:30", "11:00"), ("12:00", "13:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Friday": [("9:00", "9:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:30", "17:00")]
}

bradley_busy = {
    "Monday": [("9:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"), ("14:00", "15:00")],
    "Tuesday": [("10:30", "11:00"), ("12:00", "13:00"), ("13:30", "14:00"), ("15:30", "16:30")],
    "Wednesday": [("9:00", "10:00"), ("11:00", "13:00"), ("13:30", "14:00"), ("14:30", "17:00")],
    "Thursday": [("9:00", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Friday": [("9:00", "9:30"), ("10:00", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:30", "16:30")]
}

# Define preferences
preferences = {
    "Daniel": {"avoid_days": ["Wednesday", "Thursday"]},
    "Bradley": {"avoid_days": ["Monday", "Friday"], "avoid_tuesday_before_12": True}
}

# Find meeting time
day, time_range = find_meeting_time(daniel_busy, bradley_busy, preferences, 30)

if day and time_range:
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")