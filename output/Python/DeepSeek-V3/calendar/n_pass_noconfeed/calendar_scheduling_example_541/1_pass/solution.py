def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time strings to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Generate all busy intervals for each participant
    all_busy_intervals = []
    for schedule in participants_schedules:
        busy_intervals = []
        for busy in schedule:
            start, end = busy.split(' to ')
            busy_start = time_to_minutes(start)
            busy_end = time_to_minutes(end)
            busy_intervals.append((busy_start, busy_end))
        all_busy_intervals.append(busy_intervals)
    
    # Find all free intervals for each participant
    all_free_intervals = []
    for busy_intervals in all_busy_intervals:
        free_intervals = []
        # Sort busy intervals by start time
        busy_intervals.sort()
        
        # Check before first busy interval
        prev_end = work_start
        for start, end in busy_intervals:
            if start > prev_end:
                free_intervals.append((prev_end, start))
            prev_end = max(prev_end, end)
        # Check after last busy interval
        if prev_end < work_end:
            free_intervals.append((prev_end, work_end))
        all_free_intervals.append(free_intervals)
    
    # Find overlapping free intervals across all participants
    common_free_intervals = all_free_intervals[0]
    for free_intervals in all_free_intervals[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free_intervals) and j < len(free_intervals):
            start1, end1 = common_free_intervals[i]
            start2, end2 = free_intervals[j]
            
            # Find the overlap
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free_intervals = new_common_free
    
    # Find the first interval that can fit the meeting
    for start, end in common_free_intervals:
        if end - start >= duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + duration_minutes
            return (minutes_to_time(meeting_start), minutes_to_time(meeting_end))
    
    return None

# Input data
participants_schedules = [
    ["10:00 to 10:30", "14:30 to 16:00"],  # Kayla's schedule
    ["9:00 to 13:00", "13:30 to 15:00", "15:30 to 16:00"]  # Rebecca's schedule
]
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 60  # 1 hour
day_of_week = "Monday"

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes)

# Output
if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time}:{end_time}")
    print(day_of_week)
else:
    print("No suitable time found.")