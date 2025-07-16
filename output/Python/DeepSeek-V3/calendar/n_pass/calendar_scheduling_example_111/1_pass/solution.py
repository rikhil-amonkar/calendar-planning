def find_meeting_time(participants_schedules, day, work_hours, duration_minutes):
    # Convert work hours to minutes since midnight
    work_start = int(work_hours[0].split(':')[0]) * 60 + int(work_hours[0].split(':')[1])
    work_end = int(work_hours[1].split(':')[0]) * 60 + int(work_hours[1].split(':')[1])
    
    # Initialize the free slots for all participants
    free_slots = []
    for schedule in participants_schedules:
        # Start with the entire work day as free
        free = [(work_start, work_end)]
        
        # Subtract the busy times from the free slots
        for busy in schedule:
            busy_start = int(busy[0].split(':')[0]) * 60 + int(busy[0].split(':')[1])
            busy_end = int(busy[1].split(':')[0]) * 60 + int(busy[1].split(':')[1])
            new_free = []
            for slot in free:
                if busy_start >= slot[1] or busy_end <= slot[0]:
                    # No overlap, keep the slot
                    new_free.append(slot)
                else:
                    # Overlap, split the slot
                    if slot[0] < busy_start:
                        new_free.append((slot[0], busy_start))
                    if slot[1] > busy_end:
                        new_free.append((busy_end, slot[1]))
            free = new_free
        free_slots.append(free)
    
    # Find the intersection of all free slots
    common_free = free_slots[0]
    for slots in free_slots[1:]:
        new_common = []
        for slot1 in common_free:
            for slot2 in slots:
                start = max(slot1[0], slot2[0])
                end = min(slot1[1], slot2[1])
                if start < end:
                    new_common.append((start, end))
        common_free = new_common
    
    # Find the first slot that fits the duration
    for slot in common_free:
        if slot[1] - slot[0] >= duration_minutes:
            # Convert back to HH:MM format
            start_hh = slot[0] // 60
            start_mm = slot[0] % 60
            end_time = slot[0] + duration_minutes
            end_hh = end_time // 60
            end_mm = end_time % 60
            return f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
    
    return None

# Define the participants' schedules
participants_schedules = [
    [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("13:30", "14:00")],  # Gregory
    [],  # Natalie
    [("09:00", "11:30"), ("13:30", "17:00")],  # Christine
    [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")],  # Vincent
]

# Define the meeting day, work hours, and duration
day = "Monday"
work_hours = ("09:00", "17:00")
duration_minutes = 30

# Find the meeting time
meeting_time = find_meeting_time(participants_schedules, day, work_hours, duration_minutes)

# Output the result
print(f"{day}:{meeting_time}")