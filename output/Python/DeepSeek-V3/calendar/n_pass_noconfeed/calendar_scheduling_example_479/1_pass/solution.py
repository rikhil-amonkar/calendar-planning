def find_meeting_time(participants_schedules, day, work_hours, duration):
    # Convert work hours to minutes since midnight
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Initialize a list to keep track of busy times for all participants
    busy_slots = []
    
    for schedule in participants_schedules:
        for busy in schedule:
            start = busy[0] * 60
            end = busy[1] * 60
            busy_slots.append((start, end))
    
    # Sort the busy slots by start time
    busy_slots.sort()
    
    # Find the free slots by checking gaps between busy slots and work hours
    free_slots = []
    prev_end = work_start
    
    for start, end in busy_slots:
        if start > prev_end:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end:
        free_slots.append((prev_end, work_end))
    
    # Merge overlapping or adjacent free slots (not necessary here but good practice)
    merged_free_slots = []
    for start, end in free_slots:
        if not merged_free_slots:
            merged_free_slots.append((start, end))
        else:
            last_start, last_end = merged_free_slots[-1]
            if start <= last_end:
                merged_free_slots[-1] = (last_start, max(last_end, end))
            else:
                merged_free_slots.append((start, end))
    
    # Find the first free slot that can accommodate the meeting duration
    duration_minutes = duration * 60
    for start, end in merged_free_slots:
        if end - start >= duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            start_hour = meeting_start // 60
            start_min = meeting_start % 60
            end_hour = meeting_end // 60
            end_min = meeting_end % 60
            return (day, f"{start_hour:02d}:{start_min:02d}:{end_hour:02d}:{end_min:02d}")
    
    return None

# Define the participants' schedules in terms of busy slots (in hours)
participants_schedules = [
    [],  # Evelyn is free
    [(11.0, 12.5), (13.5, 14.5), (16.5, 17.0)],  # Joshua
    [],  # Kevin is free
    [],  # Gerald is free
    [(9.0, 9.5), (10.5, 12.0), (12.5, 13.0), (13.5, 14.0), (14.5, 15.0), (15.5, 16.0)],  # Jerry
    [(9.0, 9.5), (10.5, 12.0), (12.5, 13.0), (14.5, 15.0), (15.5, 16.5)],  # Jesse
    [(10.5, 12.5), (13.5, 14.0), (14.5, 15.0), (15.5, 16.0), (16.5, 17.0)],  # Kenneth
]

# Define work hours (9:00 to 17:00) and meeting duration (1 hour)
work_hours = (9.0, 17.0)
duration = 1.0
day = "Monday"

# Find the meeting time
result = find_meeting_time(participants_schedules, day, work_hours, duration)

# Output the result
if result:
    day, time_range = result
    print(f"{day}: {time_range}")
else:
    print("No suitable time found.")