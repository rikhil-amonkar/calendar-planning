def find_meeting_time(participants_schedules, day, work_start, work_end, duration):
    # Convert time strings to minutes since midnight for easier calculation
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
    duration_min = duration * 60
    
    # Initialize the list of busy intervals for all participants
    busy_intervals = []
    
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find the earliest available slot
    prev_end = work_start_min
    for start, end in busy_intervals:
        if start > prev_end:
            available_start = prev_end
            available_end = start
            if available_end - available_start >= duration_min:
                return (minutes_to_time(available_start), minutes_to_time(available_start + duration_min))
        prev_end = max(prev_end, end)
    
    # Check the slot after the last busy interval
    if work_end_min - prev_end >= duration_min:
        return (minutes_to_time(prev_end), minutes_to_time(prev_end + duration_min))
    
    return None

# Define the participants' schedules
participants_schedules = [
    ["12:30 to 13:30", "14:30 to 15:00", "16:30 to 17:00"],  # Olivia
    [],  # Anna
    ["09:00 to 10:00", "11:30 to 16:00", "16:30 to 17:00"],  # Virginia
    ["09:00 to 09:30", "11:00 to 11:30", "13:00 to 14:00", "14:30 to 16:00", "16:30 to 17:00"],  # Paul
]

# Define meeting parameters
day = "Monday"
work_start = "09:00"
work_end = "17:00"
duration = 1  # in hours

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_start, work_end, duration)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print(day)
else:
    print("No suitable time found.")