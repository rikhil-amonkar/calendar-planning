def find_meeting_time(participants_busy, work_hours, duration):
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start, work_end = work_hours.split(' to ')
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Initialize a list to keep track of busy intervals for all participants
    all_busy_intervals = []
    
    for person, intervals in participants_busy.items():
        for interval in intervals:
            start, end = interval.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            all_busy_intervals.append((start_min, end_min))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Find free intervals by merging busy intervals
    free_intervals = []
    prev_end = work_start_min
    
    for start, end in all_busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    if prev_end < work_end_min:
        free_intervals.append((prev_end, work_end_min))
    
    # Check each free interval for availability of duration
    for start, end in free_intervals:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' busy schedules
participants_busy = {
    "Patrick": ["9:00 to 9:30", "10:00 to 10:30", "13:30 to 14:00", "16:00 to 16:30"],
    "Kayla": ["12:30 to 13:30", "15:00 to 15:30", "16:00 to 16:30"],
    "Carl": ["10:30 to 11:00", "12:00 to 12:30", "13:00 to 13:30", "14:30 to 17:00"],
    "Christian": ["9:00 to 12:30", "13:00 to 14:00", "14:30 to 17:00"]
}

# Define work hours and meeting duration
work_hours = "9:00 to 17:00"
meeting_duration = 30  # minutes

# Find the meeting time
meeting_time = find_meeting_time(participants_busy, work_hours, meeting_duration)

# Output the result
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{{{start_time}:{end_time}}}")
    print("Monday")
else:
    print("No suitable time found.")