def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    start_hour, end_hour = work_hours
    start_time = int(start_hour * 60)  # Convert to minutes
    end_time = int(end_hour * 60)
    
    # Initialize a list to keep track of busy times for all participants
    busy_times = []
    
    for schedule in participants_schedules:
        for block in schedule:
            start_block = int(block[0] * 60)
            end_block = int(block[1] * 60)
            busy_times.append((start_block, end_block))
    
    # Sort all busy times by start time
    busy_times.sort()
    
    # Find the earliest available slot
    previous_end = start_time
    for busy_start, busy_end in busy_times:
        if busy_start > previous_end:
            available_start = previous_end
            available_end = busy_start
            if available_end - available_start >= duration_minutes:
                # Convert back to hours and minutes
                start_h = int(available_start // 60)
                start_m = int(available_start % 60)
                end_h = int((available_start + duration_minutes) // 60)
                end_m = int((available_start + duration_minutes) % 60)
                return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
        previous_end = max(previous_end, busy_end)
    
    # Check after the last busy block
    if previous_end + duration_minutes <= end_time:
        start_h = int(previous_end // 60)
        start_m = int(previous_end % 60)
        end_h = int((previous_end + duration_minutes) // 60)
        end_m = int((previous_end + duration_minutes) % 60)
        return f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}"
    
    return None

# Define participants' schedules in hours (as tuples)
gregory_schedule = [(9.0, 10.0), (10.5, 11.5), (12.5, 13.0), (13.5, 14.0)]
natalie_schedule = []
christine_schedule = [(9.0, 11.5), (13.5, 17.0)]
vincent_schedule = [(9.0, 9.5), (10.5, 12.0), (12.5, 14.0), (14.5, 17.0)]

participants_schedules = [gregory_schedule, natalie_schedule, christine_schedule, vincent_schedule]
day = "Monday"
work_hours = (9, 17)  # 9:00 to 17:00
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)

# Output the result
print(f"{day}: {meeting_time}")