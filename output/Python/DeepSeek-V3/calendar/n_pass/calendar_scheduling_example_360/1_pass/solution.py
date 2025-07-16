def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    duration = duration_minutes
    
    # Initialize the free slots for all participants
    free_slots = []
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(':'))
            busy_slots.append((start, end))
        # Sort busy slots by start time
        busy_slots.sort()
        
        # Calculate free slots by finding gaps between busy slots and work hours
        free = []
        prev_end = work_start
        for start, end in busy_slots:
            if start > prev_end:
                free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            free.append((prev_end, work_end))
        free_slots.append(free)
    
    # Find overlapping free slots across all participants
    common_free = free_slots[0]
    for participant_free in free_slots[1:]:
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(participant_free):
            start1, end1 = common_free[i]
            start2, end2 = participant_free[j]
            
            # Find overlap
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common_free
    
    # Find the first slot that can accommodate the meeting duration
    for start, end in common_free:
        if end - start >= duration:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + duration)
            return f"{day}:{meeting_start}:{meeting_end}"
    
    return "No suitable time found"

# Define the participants' schedules
participants_schedules = [
    ["10:00:10:30", "16:00:16:30"],  # Emily
    [],                              # Mason
    ["10:30:11:00", "14:00:14:30"],  # Maria
    ["9:30:10:00", "10:30:12:30", "13:30:14:00", "14:30:15:30", "16:00:17:00"],  # Carl
    ["9:30:11:00", "11:30:12:00", "12:30:13:30", "14:00:15:00", "16:00:17:00"],  # David
    ["9:30:10:30", "11:00:11:30", "12:30:13:30", "14:30:17:00"]  # Frank
]

# Define meeting parameters
day = "Monday"
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 30

# Find and print the meeting time
result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)
print(result)