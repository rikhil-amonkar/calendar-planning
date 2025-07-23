def find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration):
    # Convert all times to minutes since midnight for easier calculation
    work_start = work_hours_start[0] * 60 + work_hours_start[1]
    work_end = work_hours_end[0] * 60 + work_hours_end[1]
    
    # Initialize the free slots as the entire work day
    free_slots = [(work_start, work_end)]
    
    # Process each participant's schedule to find common free slots
    for schedule in participants_schedules:
        new_free_slots = []
        for busy_start, busy_end in schedule:
            busy_start_min = busy_start[0] * 60 + busy_start[1]
            busy_end_min = busy_end[0] * 60 + busy_end[1]
            
            updated_slots = []
            for slot_start, slot_end in free_slots:
                if busy_end_min <= slot_start or busy_start_min >= slot_end:
                    # No overlap, keep the slot as is
                    updated_slots.append((slot_start, slot_end))
                else:
                    # Split the slot around the busy time
                    if slot_start < busy_start_min:
                        updated_slots.append((slot_start, busy_start_min))
                    if busy_end_min < slot_end:
                        updated_slots.append((busy_end_min, slot_end))
            free_slots = updated_slots
    
    # Check for a slot that can accommodate the meeting duration
    meeting_duration_min = meeting_duration * 60
    for slot_start, slot_end in free_slots:
        if slot_end - slot_start >= meeting_duration_min:
            # Found a suitable slot
            meeting_start = slot_start
            meeting_end = meeting_start + meeting_duration_min
            return (meeting_start, meeting_end)
    
    return None

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the participants' schedules in (HH, MM) format
james_schedule = [
    ((11, 30), (12, 00)),
    ((14, 30), (15, 00))
]
john_schedule = [
    ((9, 30), (11, 00)),
    ((11, 30), (12, 00)),
    ((12, 30), (13, 30)),
    ((14, 30), (16, 30))
]

# Combine all participants' schedules
participants_schedules = [james_schedule, john_schedule]

# Define work hours and meeting duration
work_hours_start = (9, 00)  # 9:00 AM
work_hours_end = (17, 00)    # 5:00 PM
meeting_duration = 1          # 1 hour

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, work_hours_start, work_hours_end, meeting_duration)

if meeting_time:
    start, end = meeting_time
    start_time = format_time(start)
    end_time = format_time(end)
    print(f"Monday:{{{start_time}:{end_time}}}")
else:
    print("No suitable time found.")