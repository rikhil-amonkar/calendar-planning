def find_meeting_time(participants_schedules, work_hours, duration):
    # Convert time strings to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 540  # Subtract 540 to start from 9:00 (0 minutes)
    
    def minutes_to_time(minutes):
        total_minutes = minutes + 540
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    start_work, end_work = work_hours.split(' to ')
    work_start = time_to_minutes(start_work)
    work_end = time_to_minutes(end_work)
    
    # Initialize the free slots for all participants
    free_slots = []
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = busy.split(' to ')
            busy_start = time_to_minutes(start)
            busy_end = time_to_minutes(end)
            busy_slots.append((busy_start, busy_end))
        
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Calculate free slots
        current_time = work_start
        free = []
        for start, end in busy_slots:
            if start > current_time:
                free.append((current_time, start))
            current_time = max(current_time, end)
        if current_time < work_end:
            free.append((current_time, work_end))
        
        free_slots.append(free)
    
    # Find intersection of all free slots
    common_free = free_slots[0]
    for slots in free_slots[1:]:
        new_common = []
        i = j = 0
        while i < len(common_free) and j < len(slots):
            start1, end1 = common_free[i]
            start2, end2 = slots[j]
            
            # Find overlap
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                new_common.append((start, end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common
    
    # Find the first slot that can fit the duration
    duration_min = duration * 60
    for start, end in common_free:
        if end - start >= duration_min:
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + duration_min)
            return f"{meeting_start}:{meeting_end}"
    
    return "No suitable time found"

# Define participants' schedules
participants_schedules = [
    [],  # Diane is free all day
    ["10:30 to 11:00", "16:00 to 16:30"],  # Olivia
    ["9:00 to 9:30", "10:30 to 12:00", "12:30 to 15:00", "15:30 to 17:00"],  # Vincent
    ["9:00 to 10:30", "11:00 to 12:00", "12:30 to 17:00"],  # Steven
]

# Define work hours and meeting duration
work_hours = "9:00 to 17:00"
duration = 0.5  # half hour

# Find meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours, duration)
print(meeting_time)