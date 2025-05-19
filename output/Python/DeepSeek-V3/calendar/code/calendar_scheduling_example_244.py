def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration):
    # Convert time strings to minutes since midnight for easier calculation
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
    def subtract_busy_slots(free_slots, busy_start, busy_end):
        new_free_slots = []
        for slot_start, slot_end in free_slots:
            if busy_start >= slot_end or busy_end <= slot_start:
                new_free_slots.append((slot_start, slot_end))
            else:
                if slot_start < busy_start:
                    new_free_slots.append((slot_start, busy_start))
                if slot_end > busy_end:
                    new_free_slots.append((busy_end, slot_end))
        return new_free_slots
    
    # Process each participant's schedule
    for schedule in participants_schedules:
        for busy_start, busy_end in schedule:
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            free_slots = subtract_busy_slots(free_slots, busy_start_min, busy_end_min)
    
    # Find the first free slot that can accommodate the meeting
    meeting_duration_min = meeting_duration * 60
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration_min:
            meeting_end = slot_start + meeting_duration_min
            return minutes_to_time(slot_start), minutes_to_time(meeting_end)
    
    return None, None

# Define the participants' schedules
participants_schedules = [
    [],  # Walter has no meetings
    [("09:00", "09:30"), ("10:00", "10:30"), ("13:30", "14:30"), ("15:00", "16:00")],  # Cynthia
    [("10:00", "11:00"), ("13:00", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],  # Ann
    [("09:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],  # Catherine
    [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:30"), ("15:00", "16:00")],  # Kyle
]

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(
    participants_schedules=participants_schedules,
    work_hours_start="09:00",
    work_hours_end="17:00",
    meeting_duration=0.5
)

# Output the result
print(f"{meeting_start}:{meeting_end}:Monday")