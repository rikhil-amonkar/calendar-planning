def find_meeting_time(participants_schedules, day, work_start, work_end, duration):
    # Convert time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = int(minutes) // 60
        mm = int(minutes) % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = int(duration * 60)  # Convert to integer minutes
    
    # Initialize the list of busy intervals for all participants
    all_busy_intervals = []
    
    for person, schedules in participants_schedules.items():
        for interval in schedules:
            start, end = interval.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            all_busy_intervals.append((start_min, end_min))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Find the earliest time when everyone is free
    current_time = work_start_min
    for start, end in all_busy_intervals:
        if start > current_time:
            # Check if there's enough time before the next busy interval
            if start - current_time >= duration_min:
                meeting_end = current_time + duration_min
                return (minutes_to_time(current_time), minutes_to_time(meeting_end))
        # Update current_time to the end of this busy interval if it's later
        if end > current_time:
            current_time = end
        # If current_time exceeds work hours, break
        if current_time >= work_end_min:
            break
    
    # Check the remaining time after the last busy interval
    if work_end_min - current_time >= duration_min:
        meeting_end = current_time + duration_min
        return (minutes_to_time(current_time), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules
participants_schedules = {
    "Megan": ["9:00 to 9:30", "10:00 to 11:00", "12:00 to 12:30"],
    "Christine": ["9:00 to 9:30", "11:30 to 12:00", "13:00 to 14:00", "15:30 to 16:30"],
    "Gabriel": [],
    "Sara": ["11:30 to 12:00", "14:30 to 15:00"],
    "Bruce": ["9:30 to 10:00", "10:30 to 12:00", "12:30 to 14:00", "14:30 to 15:00", "15:30 to 16:30"],
    "Kathryn": ["10:00 to 15:30", "16:00 to 16:30"],
    "Billy": ["9:00 to 9:30", "11:00 to 11:30", "12:00 to 14:00", "14:30 to 15:30"]
}

# Parameters for the meeting
day = "Monday"
work_start = "9:00"
work_end = "17:00"
duration = 0.5  # in hours

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_start, work_end, duration)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{day}: {start_time} to {end_time}")
else:
    print("No suitable time found.")