def find_meeting_time(participants_schedules, work_hours, duration, day):
    # Convert time strings to minutes for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours.split(' to ')
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Initialize busy slots for all participants
    busy_slots = []
    for schedule in participents_schedules:
        for busy in schedule:
            start, end = busy.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_slots.append((start_min, end_min))
    
    # Sort all busy slots by start time
    busy_slots.sort()
    
    # Find all free slots
    free_slots = []
    prev_end = work_start_min
    for start, end in busy_slots:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end_min:
        free_slots.append((prev_end, work_end_min))
    
    # Check each free slot for availability
    duration_min = duration * 60
    for slot in free_slots:
        start, end = slot
        if end - start >= duration_min:
            meeting_end = start + duration_min
            return f"{minutes_to_time(start)}:{minutes_to_time(meeting_end)}", day
    
    return None, None

# Define the task parameters
participants_schedules = [
    ["12:00 to 12:30", "15:30 to 16:00"],  # Denise
    [],                                    # Angela
    ["9:00 to 11:30", "12:00 to 13:00", "14:00 to 14:30", "15:00 to 17:00"]  # Natalie
]
work_hours = "9:00 to 17:00"
meeting_duration = 0.5  # in hours
day = "Monday"

# Find the earliest meeting time
meeting_time, day = find_meeting_time(participants_schedules, work_hours, meeting_duration, day)

# Output the result
print(f"{meeting_time}:{day}")