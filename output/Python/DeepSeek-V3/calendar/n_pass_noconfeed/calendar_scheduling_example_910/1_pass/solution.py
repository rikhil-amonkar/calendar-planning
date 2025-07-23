from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def find_meeting_time(busy_slots_bryan, busy_slots_nicholas, days, duration, preferences):
    work_start = time_to_minutes(parse_time("09:00"))
    work_end = time_to_minutes(parse_time("17:00"))
    
    for day in days:
        if day in preferences["Bryan"] or day in preferences["Nicholas"]:
            continue
        
        # Get busy slots for the day
        bryan_busy = busy_slots_bryan.get(day, [])
        nicholas_busy = busy_slots_nicholas.get(day, [])
        
        # Combine and sort all busy slots
        all_busy = bryan_busy + nicholas_busy
        all_busy.sort(key=lambda x: time_to_minutes(parse_time(x[0])))
        
        # Find free slots
        prev_end = work_start
        free_slots = []
        
        for slot in all_busy:
            start = time_to_minutes(parse_time(slot[0]))
            end = time_to_minutes(parse_time(slot[1]))
            
            if start > prev_end:
                free_slots.append((prev_end, start))
            prev_end = max(prev_end, end)
        
        if prev_end < work_end:
            free_slots.append((prev_end, work_end))
        
        # Check for a slot that fits the duration
        for slot in free_slots:
            start, end = slot
            if end - start >= duration:
                meeting_start = minutes_to_time(start)
                meeting_end = minutes_to_time(start + duration)
                return day, f"{meeting_start}:{meeting_end}"
    
    return None, None

# Define busy slots
busy_slots_bryan = {
    "Thursday": [("09:30", "10:00"), ("12:30", "13:00")],
    "Friday": [("10:30", "11:00"), ("14:00", "14:30")]
}

busy_slots_nicholas = {
    "Monday": [("11:30", "12:00"), ("13:00", "15:30")],
    "Tuesday": [("09:00", "09:30"), ("11:00", "13:30"), ("14:00", "16:30")],
    "Wednesday": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
    "Thursday": [("10:30", "11:30"), ("12:00", "12:30"), ("15:00", "15:30"), ("16:30", "17:00")],
    "Friday": [("09:00", "10:30"), ("11:00", "12:00"), ("12:30", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Define preferences
preferences = {
    "Bryan": ["Tuesday"],
    "Nicholas": ["Monday", "Thursday"]
}

# Define days and duration
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
duration = 60  # minutes

# Find meeting time
day, time_range = find_meeting_time(busy_slots_bryan, busy_slots_nicholas, days, duration, preferences)

if day and time_range:
    print(f"{day}, {time_range}")
else:
    print("No suitable time found.")