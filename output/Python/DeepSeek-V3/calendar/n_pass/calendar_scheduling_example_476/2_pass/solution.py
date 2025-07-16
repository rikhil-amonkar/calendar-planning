def find_meeting_time(participants_schedules, duration_minutes=30, work_hours_start=9, work_hours_end=17):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start * 60
    work_end = work_hours_end * 60
    
    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []
    
    for participant, schedules in participants_schedules.items():
        for schedule in schedules:
            start_h, start_m = schedule[0]
            end_h, end_m = schedule[1]
            start = start_h * 60 + start_m
            end = end_h * 60 + end_m
            busy_intervals.append((start, end))
    
    # Add Roger's unavailable time (before 12:30)
    roger_unavailable = (0, 12 * 60 + 30)
    busy_intervals.append(roger_unavailable)
    
    # Sort all busy intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent busy intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                # Overlapping or adjacent intervals, merge them
                new_start = min(last_start, current_start)
                new_end = max(last_end, current_end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
    
    # Find the free intervals by looking at gaps between busy intervals and work hours
    free_intervals = []
    previous_end = work_start
    for start, end in merged:
        if start > previous_end:
            free_intervals.append((previous_end, start))
        previous_end = max(previous_end, end)
    if previous_end < work_end:
        free_intervals.append((previous_end, work_end))
    
    # Check each free interval to see if it can fit the meeting duration
    for start, end in free_intervals:
        if end - start >= duration_minutes:
            # Convert back to hours and minutes
            start_time = (start // 60, start % 60)
            end_time = ((start + duration_minutes) // 60, (start + duration_minutes) % 60)
            return start_time, end_time
    
    return None, None

# Define the participants' schedules in terms of busy intervals (start, end) in 24-hour format
participants_schedules = {
    'Daniel': [],
    'Kathleen': [((14, 30), (15, 30))],
    'Carolyn': [((12, 0), (12, 30)), ((13, 0), (13, 30))],
    'Roger': [],
    'Cheryl': [((9, 0), (9, 30)), ((10, 0), (11, 30)), ((12, 30), (13, 30)), ((14, 0), (17, 0))],
    'Virginia': [((9, 30), (11, 30)), ((12, 0), (12, 30)), ((13, 0), (13, 30)), ((14, 30), (15, 30)), ((16, 0), (17, 0))],
    'Angela': [((9, 30), (10, 0)), ((10, 30), (11, 30)), ((12, 0), (12, 30)), ((13, 0), (13, 30)), ((14, 0), (16, 30))],
}

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules)

if start_time and end_time:
    start_h, start_m = start_time
    end_h, end_m = end_time
    print(f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}")
    print("Monday")
else:
    print("No suitable time found.")