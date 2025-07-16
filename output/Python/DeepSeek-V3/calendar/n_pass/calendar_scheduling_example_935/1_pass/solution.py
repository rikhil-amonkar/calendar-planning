from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return datetime.strptime(f"{hours:02d}:{minutes:02d}", "%H:%M").time()

def get_available_slots(busy_slots, work_start, work_end, duration):
    available = []
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Sort busy slots by start time
    busy_slots.sort(key=lambda x: x[0])
    
    # Check before first busy slot
    first_busy_start = busy_slots[0][0] if busy_slots else work_end_min
    if first_busy_start - work_start_min >= duration:
        available.append((work_start_min, first_busy_start))
    
    # Check between busy slots
    for i in range(1, len(busy_slots)):
        prev_end = busy_slots[i-1][1]
        curr_start = busy_slots[i][0]
        if curr_start - prev_end >= duration:
            available.append((prev_end, curr_start))
    
    # Check after last busy slot
    if busy_slots:
        last_busy_end = busy_slots[-1][1]
        if work_end_min - last_busy_end >= duration:
            available.append((last_busy_end, work_end_min))
    else:
        available.append((work_start_min, work_end_min))
    
    return available

def find_earliest_meeting_time(terry_busy, frances_busy, days, duration, work_start, work_end, avoid_day=None):
    work_start_time = parse_time(work_start)
    work_end_time = parse_time(work_end)
    duration_min = duration
    
    for day in days:
        if avoid_day and day == avoid_day:
            continue
        
        # Get Terry's busy slots for the day
        terry_day_busy = []
        for slot in terry_busy.get(day, []):
            start = time_to_minutes(parse_time(slot[0]))
            end = time_to_minutes(parse_time(slot[1]))
            terry_day_busy.append((start, end))
        
        # Get Frances's busy slots for the day
        frances_day_busy = []
        for slot in frances_busy.get(day, []):
            start = time_to_minutes(parse_time(slot[0]))
            end = time_to_minutes(parse_time(slot[1]))
            frances_day_busy.append((start, end))
        
        # Get available slots for Terry
        terry_available = get_available_slots(terry_day_busy, work_start_time, work_end_time, duration_min)
        
        # Get available slots for Frances
        frances_available = get_available_slots(frances_day_busy, work_start_time, work_end_time, duration_min)
        
        # Find overlapping slots
        for t_start, t_end in terry_available:
            for f_start, f_end in frances_available:
                overlap_start = max(t_start, f_start)
                overlap_end = min(t_end, f_end)
                if overlap_end - overlap_start >= duration_min:
                    meeting_start = minutes_to_time(overlap_start)
                    meeting_end = minutes_to_time(overlap_start + duration_min)
                    return day, meeting_start, meeting_end
    
    return None, None, None

# Define work hours and meeting duration
work_start = "09:00"
work_end = "17:00"
duration = 30  # minutes
avoid_day = "Tuesday"  # Frances prefers to avoid Tuesday

# Define busy slots for Terry and Frances
terry_busy = {
    "Monday": [("10:30", "11:00"), ("12:30", "14:00"), ("15:00", "17:00")],
    "Tuesday": [("9:30", "10:00"), ("10:30", "11:00"), ("14:00", "14:30"), ("16:00", "16:30")],
    "Wednesday": [("9:30", "10:30"), ("11:00", "12:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
    "Thursday": [("9:30", "10:00"), ("12:00", "12:30"), ("13:00", "14:30"), ("16:00", "16:30")],
    "Friday": [("9:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")]
}

frances_busy = {
    "Monday": [("9:30", "11:00"), ("11:30", "13:00"), ("14:00", "14:30"), ("15:00", "16:00")],
    "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("13:00", "14:30"), ("15:30", "16:30")],
    "Wednesday": [("9:30", "10:00"), ("10:30", "11:00"), ("11:30", "16:00"), ("16:30", "17:00")],
    "Thursday": [("11:00", "12:30"), ("14:30", "17:00")],
    "Friday": [("9:30", "10:30"), ("11:00", "12:30"), ("13:00", "16:00"), ("16:30", "17:00")]
}

days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Find the earliest meeting time
day, start_time, end_time = find_earliest_meeting_time(
    terry_busy, frances_busy, days, duration, work_start, work_end, avoid_day
)

# Output the result
if day and start_time and end_time:
    print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
else:
    print("No suitable meeting time found.")