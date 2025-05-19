def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the free slots for all participants
    free_slots = []
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start_h, start_m = busy[0]
            end_h, end_m = busy[1]
            busy_start = start_h * 60 + start_m
            busy_end = end_h * 60 + end_m
            busy_slots.append((busy_start, busy_end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Calculate free slots based on busy slots
        free = []
        prev_end = work_start
        for busy_start, busy_end in busy_slots:
            if busy_start > prev_end:
                free.append((prev_end, busy_start))
            prev_end = max(prev_end, busy_end)
        if prev_end < work_end:
            free.append((prev_end, work_end))
        
        free_slots.append(free)
    
    # Find intersection of all free slots
    common_free = free_slots[0]
    for free in free_slots[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(free):
            start1, end1 = common_free[i]
            start2, end2 = free[j]
            
            # Find the overlapping interval
            start = max(start1, start2)
            end = min(end1, end2)
            
            if start < end:
                new_common_free.append((start, end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common_free
    
    # Find the first slot that can fit the meeting duration
    duration = duration_minutes
    for start, end in common_free:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            start_h = meeting_start // 60
            start_m = meeting_start % 60
            end_h = meeting_end // 60
            end_m = meeting_end % 60
            return (f"{start_h:02d}:{start_m:02d}:{end_h:02d}:{end_m:02d}", day)
    
    return None

# Define the participants' schedules
participants_schedules = [
    [((13, 30), (14, 00)), ((14, 30), (15, 00))],  # Jacob
    [((9, 30), (10, 00)), ((11, 30), (12, 00)), ((13, 00), (13, 30)), ((16, 00), (16, 30))],  # Diana
    [((9, 30), (10, 30)), ((11, 00), (12, 30)), ((15, 30), (16, 00))],  # Adam
    [((9, 30), (10, 00)), ((10, 30), (12, 00)), ((13, 00), (15, 30)), ((16, 00), (16, 30))],  # Angela
    [((9, 00), (9, 30)), ((10, 30), (11, 30)), ((13, 00), (15, 00)), ((16, 30), (17, 00))],  # Dennis
]

# Define meeting parameters
day = "Monday"
work_hours_start = (9, 00)
work_hours_end = (17, 00)
duration_minutes = 30

# Find the meeting time
result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)
if result:
    time_range, day = result
    print(f"{time_range} {day}")
else:
    print("No suitable time found.")