from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M").time()

def time_to_minutes(time_obj):
    return time_obj.hour * 60 + time_obj.minute

def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return datetime.strptime(f"{hours:02d}:{minutes:02d}", "%H:%M").time()

def get_available_slots(busy_slots, day_start, day_end, duration):
    available = []
    day_start_min = time_to_minutes(day_start)
    day_end_min = time_to_minutes(day_end)
    
    # Sort busy slots by start time
    busy_slots.sort(key=lambda x: x[0])
    
    # Check before first busy slot
    if busy_slots and busy_slots[0][0] > day_start_min:
        available.append((day_start_min, busy_slots[0][0]))
    
    # Check between busy slots
    for i in range(1, len(busy_slots)):
        prev_end = busy_slots[i-1][1]
        curr_start = busy_slots[i][0]
        if curr_start > prev_end:
            available.append((prev_end, curr_start))
    
    # Check after last busy slot
    if busy_slots and busy_slots[-1][1] < day_end_min:
        available.append((busy_slots[-1][1], day_end_min))
    
    # If no busy slots, the whole day is available
    if not busy_slots:
        available.append((day_start_min, day_end_min))
    
    # Filter slots that can fit the duration
    valid_slots = []
    for start, end in available:
        if end - start >= duration:
            valid_slots.append((start, end))
    
    return valid_slots

def find_earliest_meeting(brian_schedule, julia_schedule, days_order, duration):
    day_start = parse_time("09:00")
    day_end = parse_time("17:00")
    duration_min = duration * 60
    
    for day in days_order:
        # Get busy slots for Brian and Julia on this day
        brian_busy = brian_schedule.get(day, [])
        julia_busy = julia_schedule.get(day, [])
        
        # Convert busy slots to minutes
        brian_busy_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in brian_busy]
        julia_busy_min = [(time_to_minutes(s), time_to_minutes(e)) for s, e in julia_busy]
        
        # Get available slots for each
        brian_available = get_available_slots(brian_busy_min, day_start, day_end, duration_min)
        julia_available = get_available_slots(julia_busy_min, day_start, day_end, duration_min)
        
        # Find overlapping available slots
        for b_start, b_end in brian_available:
            for j_start, j_end in julia_available:
                overlap_start = max(b_start, j_start)
                overlap_end = min(b_end, j_end)
                if overlap_end - overlap_start >= duration_min:
                    return day, minutes_to_time(overlap_start), minutes_to_time(overlap_start + duration_min)
    
    return None, None, None

def main():
    # Define schedules
    brian_schedule = {
        "Monday": [("09:30", "10:00"), ("12:30", "14:30"), ("15:30", "16:00")],
        "Tuesday": [("09:00", "09:30")],
        "Wednesday": [("12:30", "14:00"), ("16:30", "17:00")],
        "Thursday": [("11:00", "11:30"), ("13:00", "13:30"), ("16:30", "17:00")],
        "Friday": [("09:30", "10:00"), ("10:30", "11:00"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
    
    julia_schedule = {
        "Monday": [("09:00", "10:00"), ("11:00", "11:30"), ("12:30", "13:00"), ("15:30", "16:00")],
        "Tuesday": [("13:00", "14:00"), ("16:00", "16:30")],
        "Wednesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
        "Thursday": [("09:00", "10:30"), ("11:00", "17:00")],
        "Friday": [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")]
    }
    
    # Brian prefers to avoid Monday, so we check other days first
    days_order = ["Tuesday", "Wednesday", "Thursday", "Friday", "Monday"]
    duration = 1  # 1 hour
    
    day, start_time, end_time = find_earliest_meeting(brian_schedule, julia_schedule, days_order, duration)
    
    if day and start_time and end_time:
        print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()