def find_meeting_time(participants_schedules, day, work_start, work_end, duration):
    # Convert time strings to minutes since start of day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm
    
    # Convert minutes back to time string
    def minutes_to_time(minutes):
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"
    
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration_min = duration * 60
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start_min, work_end_min)]
    
    # For each participant, subtract their busy times from the free slots
    for schedule in participants_schedules:
        new_free_slots = []
        for busy_start, busy_end in schedule:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            temp_slots = []
            for slot_start, slot_end in free_slots:
                if busy_end_min <= slot_start or busy_start_min >= slot_end:
                    # No overlap, keep the slot
                    temp_slots.append((slot_start, slot_end))
                else:
                    # Overlap, split the slot
                    if slot_start < busy_start_min:
                        temp_slots.append((slot_start, busy_start_min))
                    if slot_end > busy_end_min:
                        temp_slots.append((busy_end_min, slot_end))
            free_slots = temp_slots.copy()
    
    # Find the first slot that can accommodate the meeting duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            return f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    
    return None

# Define the participants' schedules
julie_schedule = [
    ("09:00", "09:30"),
    ("11:00", "11:30"),
    ("12:00", "12:30"),
    ("13:30", "14:00"),
    ("16:00", "17:00")
]

sean_schedule = [
    ("09:00", "09:30"),
    ("13:00", "13:30"),
    ("15:00", "15:30"),
    ("16:00", "16:30")
]

lori_schedule = [
    ("10:00", "10:30"),
    ("11:00", "13:00"),
    ("15:30", "17:00")
]

# Combine all schedules
participants_schedules = [julie_schedule, sean_schedule, lori_schedule]

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, "Monday", "09:00", "17:00", 1)

# Output the result
print(f"{meeting_time}:Monday")