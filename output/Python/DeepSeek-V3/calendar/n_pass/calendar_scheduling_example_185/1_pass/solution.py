def find_meeting_time(participants_schedules, preferences, duration_minutes, work_hours_start, work_hours_end):
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
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        busy_slots = []
        for busy in schedule:
            start, end = map(time_to_minutes, busy.split(' to '))
            busy_slots.append((start, end))
        
        # Sort busy slots by start time
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
            slot_start, slot_end = free_slots[i]
            curr_start, curr_end = current_free[j]
            
            # Find overlap
            overlap_start = max(slot_start, curr_start)
            overlap_end = min(slot_end, curr_end)
            
            if overlap_start < overlap_end:
                new_free_slots.append((overlap_start, overlap_end))
            
            # Move the pointer which ends first
            if slot_end < curr_end:
                i += 1
            else:
                j += 1
        
        free_slots = new_free_slots
    
    # Apply preferences
    preferred_slots = []
    for start, end in free_slots:
        # Check if the slot meets preferences
        if 'before' in preferences and preferences['before']:
            avoid_before = time_to_minutes(preferences['before'])
            if end <= avoid_before:
                continue  # Skip slots entirely before the avoid time
            if start < avoid_before:
                start = avoid_before  # Adjust start time
        
        if start + duration_minutes <= end:
            preferred_slots.append((start, end))
    
    # Find the earliest possible slot that fits the duration
    for start, end in preferred_slots:
        if end - start >= duration_minutes:
            meeting_start = start
            meeting_end = meeting_start + duration_minutes
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    
    return None, None

# Define the participants' schedules
participants_schedules = [
    ["10:00 to 10:30", "11:00 to 12:00", "16:00 to 16:30"],  # Kimberly
    [],  # Megan
    ["10:00 to 11:00", "11:30 to 15:00", "16:00 to 16:30"],  # Marie
    ["09:30 to 10:00", "10:30 to 14:30", "15:30 to 17:00"],  # Diana
]

# Define preferences
preferences = {
    'before': '10:00',  # Megan prefers to avoid meetings before 10:00
}

# Define meeting details
duration_minutes = 30
work_hours_start = "09:00"
work_hours_end = "17:00"

# Find the meeting time
start_time, end_time = find_meeting_time(participants_schedules, preferences, duration_minutes, work_hours_start, work_hours_end)

# Output the result
if start_time and end_time:
    print(f"{start_time}:{end_time}")
    print("Monday")
else:
    print("No suitable time found.")