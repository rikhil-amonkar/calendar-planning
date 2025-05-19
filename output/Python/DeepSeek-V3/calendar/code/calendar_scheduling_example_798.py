def find_meeting_time(nancy_schedule, jose_schedule, days, work_hours, duration):
    start_work, end_work = work_hours
    duration_minutes = duration * 60
    
    for day in days:
        # Initialize free slots for the day
        nancy_free = get_free_slots(nancy_schedule.get(day, []), start_work, end_work)
        jose_free = get_free_slots(jose_schedule.get(day, []), start_work, end_work)
        
        # Find overlapping free slots
        overlapping = find_overlapping_slots(nancy_free, jose_free, duration_minutes)
        
        if overlapping:
            # Return the earliest possible slot
            start, end = overlapping[0]
            return day, start, end
    
    return None

def get_free_slots(busy_slots, work_start, work_end):
    # Convert time to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Process busy slots
    busy_intervals = []
    for slot in busy_slots:
        start, end = slot.split(' to ')
        start_min = time_to_minutes(start)
        end_min = time_to_minutes(end)
        busy_intervals.append((start_min, end_min))
    
    # Sort busy intervals by start time
    busy_intervals.sort()
    
    # Find free intervals
    free_intervals = []
    prev_end = work_start_min
    
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        free_intervals.append((prev_end, work_end_min))
    
    # Convert back to time strings
    free_slots = []
    for start, end in free_intervals:
        free_slots.append((minutes_to_time(start), minutes_to_time(end)))
    
    return free_slots

def find_overlapping_slots(slots1, slots2, duration):
    # Convert time to minutes for comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    overlapping = []
    
    for s1_start, s1_end in slots1:
        s1_start_min = time_to_minutes(s1_start)
        s1_end_min = time_to_minutes(s1_end)
        
        for s2_start, s2_end in slots2:
            s2_start_min = time_to_minutes(s2_start)
            s2_end_min = time_to_minutes(s2_end)
            
            # Find overlap
            overlap_start = max(s1_start_min, s2_start_min)
            overlap_end = min(s1_end_min, s2_end_min)
            
            if overlap_start < overlap_end and (overlap_end - overlap_start) >= duration:
                overlapping.append((overlap_start, overlap_end))
    
    # Sort overlapping slots by start time
    overlapping.sort()
    
    # Convert back to time strings
    result = []
    for start, end in overlapping:
        start_time = minutes_to_time(start)
        end_time = minutes_to_time(start + duration)
        result.append((start_time, end_time))
    
    return result

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define schedules
nancy_schedule = {
    'Monday': ['10:00 to 10:30', '11:30 to 12:30', '13:30 to 14:00', '14:30 to 15:30', '16:00 to 17:00'],
    'Tuesday': ['9:30 to 10:30', '11:00 to 11:30', '12:00 to 12:30', '13:00 to 13:30', '15:30 to 16:00'],
    'Wednesday': ['10:00 to 11:30', '13:30 to 16:00']
}

jose_schedule = {
    'Monday': ['9:00 to 17:00'],
    'Tuesday': ['9:00 to 17:00'],
    'Wednesday': ['9:00 to 9:30', '10:00 to 12:30', '13:30 to 14:30', '15:00 to 17:00']
}

# Define parameters
days = ['Monday', 'Tuesday', 'Wednesday']
work_hours = ('9:00', '17:00')
duration = 30  # minutes

# Find meeting time
result = find_meeting_time(nancy_schedule, jose_schedule, days, work_hours, duration)

if result:
    day, start, end = result
    print(f"{day}: {start}:{end}")
else:
    print("No suitable time found.")