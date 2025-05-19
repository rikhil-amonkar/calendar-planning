def find_meeting_time(participants_schedules, work_hours, duration_minutes, day):
    # Convert all time slots to minutes since start of the day
    work_start = work_hours[0]
    work_end = work_hours[1]
    
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Collect all busy intervals for all participants
    busy_intervals = []
    for schedule in participants_schedules:
        for busy in schedule:
            start, end = map(time_to_minutes, busy)
            busy_intervals.append((start, end))
    
    # Add boundaries as busy intervals to avoid scheduling outside work hours
    busy_intervals.append((work_start_min - 60, work_start_min))  # before work starts
    busy_intervals.append((work_end_min, work_end_min + 60))      # after work ends
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Find available slots between merged busy intervals
    available_slots = []
    prev_end = work_start_min
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check for available slots after last busy interval
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Find the first available slot that can fit the meeting
    duration = duration_minutes
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return f"{start_time}:{end_time}"
    
    return None

# Define the participants' schedules
michael_schedule = [
    ("09:30", "10:30"),
    ("15:00", "15:30"),
    ("16:00", "16:30"),
]

eric_schedule = []

arthur_schedule = [
    ("09:00", "12:00"),
    ("13:00", "15:00"),
    ("15:30", "16:00"),
    ("16:30", "17:00"),
]

participants_schedules = [michael_schedule, eric_schedule, arthur_schedule]
work_hours = ("09:00", "17:00")
duration_minutes = 30
day = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration_minutes, day)

# Output the result
print(f"{day}:{meeting_time}")