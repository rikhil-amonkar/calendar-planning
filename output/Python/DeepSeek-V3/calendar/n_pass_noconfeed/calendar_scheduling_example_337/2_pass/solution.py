def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time strings to minutes since start of day for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to HH:MM format
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes
    
    # Initialize the list of busy intervals for all participants
    all_busy_intervals = []
    
    for schedule in participants_schedules:
        busy_intervals = []
        for meeting in schedule:
            # Split meeting string into start and end times (using hyphen as separator)
            start_str, end_str = meeting.split('-')
            start = time_to_minutes(start_str)
            end = time_to_minutes(end_str)
            busy_intervals.append((start, end))
        all_busy_intervals.append(busy_intervals)
    
    # Find all possible free intervals for each participant
    all_free_intervals = []
    for busy_intervals in all_busy_intervals:
        free_intervals = []
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Check before first meeting
        if not busy_intervals:
            free_intervals.append((work_start, work_end))
        else:
            first_start, first_end = busy_intervals[0]
            if work_start < first_start:
                free_intervals.append((work_start, first_start))
            
            # Check between meetings
            for i in range(1, len(busy_intervals)):
                prev_end = busy_intervals[i-1][1]
                curr_start = busy_intervals[i][0]
                if prev_end < curr_start:
                    free_intervals.append((prev_end, curr_start))
            
            # Check after last meeting
            last_start, last_end = busy_intervals[-1]
            if last_end < work_end:
                free_intervals.append((last_end, work_end))
        
        all_free_intervals.append(free_intervals)
    
    # Find overlapping free intervals across all participants
    common_free_intervals = all_free_intervals[0]
    for free_intervals in all_free_intervals[1:]:
        new_common = []
        for common_start, common_end in common_free_intervals:
            for free_start, free_end in free_intervals:
                overlap_start = max(common_start, free_start)
                overlap_end = min(common_end, free_end)
                if overlap_start < overlap_end:
                    new_common.append((overlap_start, overlap_end))
        common_free_intervals = new_common
        if not common_free_intervals:
            break
    
    # Find the first common free interval that can fit the meeting
    for interval in common_free_intervals:
        start, end = interval
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Define the participants' schedules with correct format (using hyphens)
participants_schedules = [
    ["11:30-12:00", "14:00-14:30"],  # John
    ["12:00-12:30", "14:00-15:00", "15:30-16:00"],  # Megan
    [],  # Brandon
    ["09:00-09:30", "10:00-10:30", "11:00-14:30", "15:00-16:00", "16:30-17:00"],  # Kimberly
    ["10:00-11:00", "11:30-14:00", "15:00-15:30"],  # Sean
    ["09:00-09:30", "10:30-12:00", "13:00-14:30", "16:00-16:30"],  # Lori
]

# Define meeting parameters
day = "Monday"
work_hours_start = "09:00"
work_hours_end = "17:00"
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{start}-{end}")
    print(day)
else:
    print("No suitable time found.")