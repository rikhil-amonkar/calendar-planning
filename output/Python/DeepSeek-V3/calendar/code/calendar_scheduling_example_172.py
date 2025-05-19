def find_meeting_time(participants_busy, work_hours, duration_minutes):
    # Convert all time strings to minutes since 9:00 (assuming work_hours start at 9:00)
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return (hh - 9) * 60 + mm  # Subtract 9 to start from 0 at 9:00
    
    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])
    duration = duration_minutes
    
    # Initialize free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's busy slots
    for busy_slots in participants_busy:
        new_free_slots = []
        for busy_start, busy_end in busy_slots:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            updated_free_slots = []
            for slot_start, slot_end in free_slots:
                if busy_end_min <= slot_start or busy_start_min >= slot_end:
                    # No overlap, keep the slot
                    updated_free_slots.append((slot_start, slot_end))
                else:
                    # Overlap, split the slot
                    if slot_start < busy_start_min:
                        updated_free_slots.append((slot_start, busy_start_min))
                    if busy_end_min < slot_end:
                        updated_free_slots.append((busy_end_min, slot_end))
            free_slots = updated_free_slots
        if not free_slots:
            return None  # No common free time
    
    # Find the first slot that fits the duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            def minutes_to_time(minutes):
                hh = 9 + minutes // 60
                mm = minutes % 60
                return f"{hh:02d}:{mm:02d}"
            start_time = minutes_to_time(meeting_start)
            end_time = minutes_to_time(meeting_end)
            return (start_time, end_time)
    return None

# Define work hours and meeting duration
work_hours = ("9:00", "17:00")
duration_minutes = 30

# Define busy slots for each participant (converted to HH:MM format)
participants_busy = [
    # Patrick's busy slots
    [("9:00", "9:30"), ("10:00", "10:30"), ("13:30", "14:00"), ("16:00", "16:30")],
    # Kayla's busy slots
    [("12:30", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    # Carl's busy slots
    [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "17:00")],
    # Christian's busy slots
    [("9:00", "12:30"), ("13:00", "14:00"), ("14:30", "17:00")],
]

# Find meeting time
meeting_time = find_meeting_time(participants_busy, work_hours, duration_minutes)

# Output the result
if meeting_time:
    start, end = meeting_time
    print(f"{start}:{end}")
    print("Monday")
else:
    print("No suitable time found.")