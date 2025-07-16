def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    """
    Finds a meeting time that fits all participants' schedules.
    
    Args:
        participants_schedules: List of lists of blocked time ranges for each participant.
        day: Day of the week for the meeting.
        work_hours: Tuple of (start_hour, end_hour) in 24-hour format.
        duration_minutes: Duration of the meeting in minutes.
    
    Returns:
        A tuple of (day, start_time, end_time) if a slot is found, otherwise None.
    """
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours[0] * 60
    work_end = work_hours[1] * 60
    
    # Initialize a list to keep track of all blocked times
    blocked_times = []
    
    # Process each participant's schedule
    for schedule in participants_schedules:
        for block in schedule:
            start_h, start_m, end_h, end_m = block
            start = start_h * 60 + start_m
            end = end_h * 60 + end_m
            blocked_times.append((start, end))
    
    # Sort all blocked times by start time
    blocked_times.sort()
    
    # Merge overlapping or adjacent blocked times
    merged = []
    for start, end in blocked_times:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))
    
    # Check for available slots between work hours and blocked times
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            # Check if the gap is enough for the meeting
            if start - prev_end >= duration_minutes:
                meeting_start = prev_end
                meeting_end = meeting_start + duration_minutes
                # Convert back to hours and minutes
                start_h = meeting_start // 60
                start_m = meeting_start % 60
                end_h = meeting_end // 60
                end_m = meeting_end % 60
                return (day, f"{start_h:02d}:{start_m:02d}", f"{end_h:02d}:{end_m:02d}")
        prev_end = max(prev_end, end)
    
    # Check after the last blocked time
    if work_end - prev_end >= duration_minutes:
        meeting_start = prev_end
        meeting_end = meeting_start + duration_minutes
        start_h = meeting_start // 60
        start_m = meeting_start % 60
        end_h = meeting_end // 60
        end_m = meeting_end % 60
        return (day, f"{start_h:02d}:{start_m:02d}", f"{end_h:02d}:{end_m:02d}")
    
    return None

# Define the participants' schedules
participants_schedules = [
    [(9, 30, 10, 0), (10, 30, 11, 0)],  # Joe
    [(11, 30, 12, 0), (15, 0, 15, 30)],  # Keith
    [(9, 0, 9, 30), (13, 0, 13, 30)],    # Patricia
    [(9, 0, 11, 0), (11, 30, 16, 30)],   # Nancy
    [(9, 0, 10, 0), (10, 30, 11, 0), (11, 30, 12, 30), (13, 0, 14, 0), 
     (14, 30, 15, 0), (15, 30, 16, 0), (16, 30, 17, 0)]  # Pamela
]

# Define meeting parameters
day = "Monday"
work_hours = (9, 17)  # 9:00 to 17:00
duration_minutes = 30

# Find the meeting time
result = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)

# Output the result
if result:
    day, start_time, end_time = result
    print(f"{day}: {start_time}:{end_time}")
else:
    print("No suitable time found.")