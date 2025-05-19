def find_meeting_time(participants_schedules, day, work_start, work_end, duration_minutes):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    
    # Initialize a list to track busy intervals for all participants
    all_busy_intervals = []
    
    for schedule in participants_schedules:
        for interval in schedule:
            start, end = map(time_to_minutes, interval.split(' to '))
            all_busy_intervals.append((start, end))
    
    # Sort all busy intervals by start time
    all_busy_intervals.sort()
    
    # Find the earliest available slot
    current_time = work_start_min
    for start, end in all_busy_intervals:
        if start > current_time and start - current_time >= duration_minutes:
            # Found a slot
            meeting_start = current_time
            meeting_end = meeting_start + duration_minutes
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
        current_time = max(current_time, end)
    
    # Check after the last busy interval
    if work_end_min - current_time >= duration_minutes:
        meeting_start = current_time
        meeting_end = meeting_start + duration_minutes
        def minutes_to_time(minutes):
            hh = minutes // 60
            mm = minutes % 60
            return f"{hh:02d}:{mm:02d}"
        return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    
    return None

# Define participants' schedules
participants_schedules = [
    ["11:30 to 12:00", "14:30 to 15:00"],  # Joan
    ["9:00 to 10:00", "14:00 to 14:30", "16:00 to 16:30"],  # Megan
    [],  # Austin
    ["9:30 to 10:00", "11:30 to 12:00", "13:30 to 14:00", "16:00 to 16:30"],  # Betty
    ["9:00 to 11:00", "12:00 to 13:00", "14:00 to 15:00"],  # Judith
    ["9:30 to 10:00", "11:30 to 12:30", "13:00 to 14:00", "15:00 to 15:30", "16:00 to 17:00"],  # Terry
    ["9:30 to 10:00", "10:30 to 11:00", "11:30 to 13:00", "14:00 to 16:00", "16:30 to 17:00"],  # Kathryn
]

day = "Monday"
work_start = "9:00"
work_end = "17:00"
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_start, work_end, duration_minutes)

if meeting_time:
    start, end = meeting_time.split(':')
    print(f"{{{start}:{end}}} {day}")
else:
    print("No suitable time found.")