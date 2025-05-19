def find_meeting_time(participants_schedules, duration, work_hours_start, work_hours_end):
    # Convert time strings to minutes since 9:00 (540 minutes)
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
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Function to subtract busy slots from free slots
    def subtract_busy(free_slots, busy_start, busy_end):
        new_free_slots = []
        for slot_start, slot_end in free_slots:
            if busy_end <= slot_start or busy_start >= slot_end:
                new_free_slots.append((slot_start, slot_end))
            else:
                if slot_start < busy_start:
                    new_free_slots.append((slot_start, busy_start))
                if slot_end > busy_end:
                    new_free_slots.append((busy_end, slot_end))
        return new_free_slots
    
    # Process each participant's schedule
    for schedule in participants_schedules:
        for busy in schedule:
            busy_start, busy_end = map(time_to_minutes, busy.split(' to '))
            free_slots = subtract_busy(free_slots, busy_start, busy_end)
    
    # Find the first slot that fits the duration
    duration_minutes = duration * 60
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= duration_minutes:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_minutes
            return minutes_to_time(meeting_start), minutes_to_time(meeting_end)
    
    return None, None

# Define participants' schedules
participants_schedules = [
    # Danielle's schedule
    ["9:00 to 10:00", "10:30 to 11:00", "14:30 to 15:00", "15:30 to 16:00", "16:30 to 17:00"],
    # Bruce's schedule
    ["11:00 to 11:30", "12:30 to 13:00", "14:00 to 14:30", "15:30 to 16:00"],
    # Eric's schedule
    ["9:00 to 9:30", "10:00 to 11:00", "11:30 to 13:00", "14:30 to 15:30"]
]

# Find meeting time
meeting_start, meeting_end = find_meeting_time(participants_schedules, 1, "9:00", "17:00")

# Output the result
print(f"{meeting_start}:{meeting_end}:Monday")