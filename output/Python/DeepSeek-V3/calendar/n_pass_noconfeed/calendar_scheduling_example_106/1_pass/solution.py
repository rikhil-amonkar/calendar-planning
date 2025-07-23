def find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day):
    # Convert time strings to minutes since midnight for easier comparison
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration_minutes = meeting_duration * 60
    
    # Initialize the list of busy intervals for all participants
    all_busy_intervals = []
    for schedule in participants_schedules:
        busy_intervals = []
        for block in schedule:
            start, end = map(time_to_minutes, block.split(' to '))
            busy_intervals.append((start, end))
        all_busy_intervals.append(busy_intervals)
    
    # Find all free intervals for each participant
    all_free_intervals = []
    for busy_intervals in all_busy_intervals:
        free_intervals = []
        # Start from work_start
        prev_end = work_start
        for start, end in sorted(busy_intervals):
            if start > prev_end:
                free_intervals.append((prev_end, start))
            prev_end = max(prev_end, end)
        # Check the interval after last busy block
        if prev_end < work_end:
            free_intervals.append((prev_end, work_end))
        all_free_intervals.append(free_intervals)
    
    # Find overlapping free intervals across all participants
    common_free_intervals = all_free_intervals[0]
    for free_intervals in all_free_intervals[1:]:
        new_common = []
        i = j = 0
        while i < len(common_free_intervals) and j < len(free_intervals):
            start1, end1 = common_free_intervals[i]
            start2, end2 = free_intervals[j]
            # Find the overlap
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            if overlap_start < overlap_end:
                new_common.append((overlap_start, overlap_end))
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free_intervals = new_common
    
    # Find the first interval that can fit the meeting duration
    for start, end in common_free_intervals:
        if end - start >= duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + duration_minutes
            return (f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}", day)
    
    return None

# Define the participants' schedules
participants_schedules = [
    ["12:30 to 13:30", "14:30 to 15:00", "16:30 to 17:00"],  # Olivia
    [],  # Anna
    ["09:00 to 10:00", "11:30 to 16:00", "16:30 to 17:00"],  # Virginia
    ["09:00 to 09:30", "11:00 to 11:30", "13:00 to 14:00", "14:30 to 16:00", "16:30 to 17:00"]  # Paul
]

# Define meeting parameters
meeting_duration = 1  # in hours
work_hours_start = "09:00"
work_hours_end = "17:00"
day = "Monday"

# Find the meeting time
result = find_meeting_time(participants_schedules, meeting_duration, work_hours_start, work_hours_end, day)
if result:
    time_range, day = result
    print(f"{time_range} {day}")
else:
    print("No suitable time found.")