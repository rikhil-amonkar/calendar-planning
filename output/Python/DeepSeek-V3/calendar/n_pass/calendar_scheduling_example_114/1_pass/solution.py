def find_meeting_time(participants_schedules, day, work_start, work_end, duration):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration * 60
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for person, schedules in participants_schedules.items():
        for interval in schedules:
            start, end = interval.split(' to ')
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals.append((start_min, end_min))
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Find all free intervals by checking gaps between busy intervals
    free_intervals = []
    prev_end = work_start_min
    
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    
    # Check the interval after the last busy interval until work_end
    if prev_end < work_end_min:
        free_intervals.append((prev_end, work_end_min))
    
    # Find the first free interval that can accommodate the meeting duration
    for start, end in free_intervals:
        if end - start >= duration_min:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + duration_min)
            return f"{day}: {meeting_start}:{meeting_end}"
    
    return "No suitable time found."

# Define the participants' schedules
participants_schedules = {
    "Stephanie": ["10:00 to 10:30", "16:00 to 16:30"],
    "Cheryl": ["10:00 to 10:30", "11:30 to 12:00", "13:30 to 14:00", "16:30 to 17:00"],
    "Bradley": ["9:30 to 10:00", "10:30 to 11:30", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 17:00"],
    "Steven": ["9:00 to 12:00", "13:00 to 13:30", "14:30 to 17:00"]
}

# Define meeting parameters
day = "Monday"
work_start = "9:00"
work_end = "17:00"
duration = 1  # in hours

# Find and print the meeting time
print(find_meeting_time(participants_schedules, day, work_start, work_end, duration))