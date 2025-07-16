def find_meeting_time(participants_schedules, meeting_duration_minutes, work_hours_start, work_hours_end):
    # Convert all time slots to minutes since start of the day for easier calculation
    def time_to_minutes(time_str):
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)

    # Initialize the free slots for the entire work day
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

    # Process each participant's busy slots
    for participant, busy_slots in participants_schedules.items():
        for busy_slot in busy_slots:
            busy_start = time_to_minutes(busy_slot[0])
            busy_end = time_to_minutes(busy_slot[1])
            free_slots = subtract_busy_slots(free_slots, busy_start, busy_end)

    # Find the first free slot that can accommodate the meeting duration
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration_minutes:
            return slot_start, slot_start + meeting_duration_minutes

    return None

def minutes_to_time(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define the participants' schedules
participants_schedules = {
    "Diane": [("09:30", "10:00"), ("14:30", "15:00")],
    "Jack": [("13:30", "14:00"), ("14:30", "15:00")],
    "Eugene": [("09:00", "10:00"), ("10:30", "11:30"), ("12:00", "14:30"), ("15:00", "16:30")],
    "Patricia": [("09:30", "10:30"), ("11:00", "12:00"), ("12:30", "14:00"), ("15:00", "16:30")],
}

meeting_duration_minutes = 30
work_hours_start = "09:00"
work_hours_end = "17:00"
day_of_week = "Monday"

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, meeting_duration_minutes, work_hours_start, work_hours_end)

if meeting_time:
    start_time, end_time = meeting_time
    start_time_str = minutes_to_time(start_time)
    end_time_str = minutes_to_time(end_time)
    print(f"{day_of_week}: {start_time_str}:{end_time_str}")
else:
    print("No suitable time found.")