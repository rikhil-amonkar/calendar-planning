def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes):
    # Convert all time strings to minutes since start of the day
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(':'))
            busy_slots.append((start, end))
        
        # Sort the busy slots by start time
        busy_slots.sort()
        
        # Calculate free slots for this participant
        current_free = []
        prev_end = work_start
        for start, end in busy_slots:
            if start > prev_end:
                current_free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            current_free.append((prev_end, work_end))
        
        # Intersect current_free with existing free_slots
        new_free_slots = []
        i = j = 0
        while i < len(free_slots) and j < len(current_free):
            start1, end1 = free_slots[i]
            start2, end2 = current_free[j]
            
            # Find the overlap
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                new_free_slots.append((start, end))
            
            # Move the pointer which ends first
            if end1 < end2:
                i += 1
            else:
                j += 1
        
        free_slots = new_free_slots
    
    # Find the first slot that can fit the meeting duration
    for start, end in free_slots:
        if end - start >= duration_minutes:
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            
            meeting_start = minutes_to_time(start)
            meeting_end = minutes_to_time(start + duration_minutes)
            return meeting_start, meeting_end
    
    return None

# Define the participants' schedules
participants_schedules = [
    # Julie's schedule
    ["9:00:9:30", "11:00:11:30", "12:00:12:30", "13:30:14:00", "16:00:17:00"],
    # Sean's schedule
    ["9:00:9:30", "13:00:13:30", "15:00:15:30", "16:00:16:30"],
    # Lori's schedule
    ["10:00:10:30", "11:00:13:00", "15:30:17:00"]
]

# Define work hours and meeting duration
work_hours_start = "9:00"
work_hours_end = "17:00"
duration_minutes = 60  # 1 hour

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, duration_minutes)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}")
    print("Monday")
else:
    print("No suitable time found.")