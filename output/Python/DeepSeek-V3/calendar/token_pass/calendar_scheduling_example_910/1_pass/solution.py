from datetime import datetime, timedelta

def parse_time(s):
    return datetime.strptime(s, "%H:%M")

def time_range(start, end):
    # returns list of (start, end) as datetime objects for easier comparison
    return (parse_time(start), parse_time(end))

def add_minutes(t, minutes):
    return t + timedelta(minutes=minutes)

def schedule_meeting(busy1, busy2, preferences1, preferences2, duration_minutes=60, work_start="09:00", work_end="17:00"):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start_t = parse_time(work_start)
    work_end_t = parse_time(work_end)
    
    # Convert busy times to datetime ranges per day
    busy1_set = {day: [] for day in days}
    busy2_set = {day: [] for day in days}
    
    # Bryan's meetings
    busy1_set["Thursday"].append(time_range("09:30", "10:00"))
    busy1_set["Thursday"].append(time_range("12:30", "13:00"))
    busy1_set["Friday"].append(time_range("10:30", "11:00"))
    busy1_set["Friday"].append(time_range("14:00", "14:30"))
    
    # Nicholas's meetings
    busy2_set["Monday"].append(time_range("11:30", "12:00"))
    busy2_set["Monday"].append(time_range("13:00", "15:30"))
    busy2_set["Tuesday"].append(time_range("09:00", "09:30"))
    busy2_set["Tuesday"].append(time_range("11:00", "13:30"))
    busy2_set["Tuesday"].append(time_range("14:00", "16:30"))
    busy2_set["Wednesday"].append(time_range("09:00", "09:30"))
    busy2_set["Wednesday"].append(time_range("10:00", "11:00"))
    busy2_set["Wednesday"].append(time_range("11:30", "13:30"))
    busy2_set["Wednesday"].append(time_range("14:00", "14:30"))
    busy2_set["Wednesday"].append(time_range("15:00", "16:30"))
    busy2_set["Thursday"].append(time_range("10:30", "11:30"))
    busy2_set["Thursday"].append(time_range("12:00", "12:30"))
    busy2_set["Thursday"].append(time_range("15:00", "15:30"))
    busy2_set["Thursday"].append(time_range("16:30", "17:00"))
    busy2_set["Friday"].append(time_range("09:00", "10:30"))
    busy2_set["Friday"].append(time_range("11:00", "12:00"))
    busy2_set["Friday"].append(time_range("12:30", "14:30"))
    busy2_set["Friday"].append(time_range("15:30", "16:00"))
    busy2_set["Friday"].append(time_range("16:30", "17:00"))
    
    # Find free slots
    for day in days:
        # Skip due to preferences
        if day in preferences1 or day in preferences2:
            continue
        
        # Get busy times for this day
        busy_times = busy1_set[day] + busy2_set[day]
        # Sort by start time
        busy_times.sort(key=lambda x: x[0])
        
        # Find free intervals within work hours
        free_start = work_start_t
        for busy_start, busy_end in busy_times:
            if busy_start > free_start:
                # Check if slot long enough
                if (busy_start - free_start).total_seconds() >= duration_minutes * 60:
                    # Found a slot
                    return day, free_start.strftime("%H:%M"), add_minutes(free_start, duration_minutes).strftime("%H:%M")
            # Move free_start to after this busy period
            if busy_end > free_start:
                free_start = busy_end
        # Check after last busy period until work_end
        if (work_end_t - free_start).total_seconds() >= duration_minutes * 60:
            return day, free_start.strftime("%H:%M"), add_minutes(free_start, duration_minutes).strftime("%H:%M")
    
    # If no slot respecting preferences, try all days
    for day in days:
        busy_times = busy1_set[day] + busy2_set[day]
        busy_times.sort(key=lambda x: x[0])
        free_start = work_start_t
        for busy_start, busy_end in busy_times:
            if busy_start > free_start:
                if (busy_start - free_start).total_seconds() >= duration_minutes * 60:
                    return day, free_start.strftime("%H:%M"), add_minutes(free_start, duration_minutes).strftime("%H:%M")
            if busy_end > free_start:
                free_start = busy_end
        if (work_end_t - free_start).total_seconds() >= duration_minutes * 60:
            return day, free_start.strftime("%H:%M"), add_minutes(free_start, duration_minutes).strftime("%H:%M")
    
    return None

# Preferences: Bryan avoid Tuesday, Nicholas avoid Monday and Thursday
preferences_bryan = ["Tuesday"]
preferences_nicholas = ["Monday", "Thursday"]

result = schedule_meeting([], [], preferences_bryan, preferences_nicholas, 60)
if result:
    day, start, end = result
    print(f"{day} {start}:{end}")
else:
    print("No suitable slot found")