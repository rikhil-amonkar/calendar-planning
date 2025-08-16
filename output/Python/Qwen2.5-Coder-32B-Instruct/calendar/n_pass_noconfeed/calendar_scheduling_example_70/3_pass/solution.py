from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available slots for each participant
    available_slots = {}
    for person, blocks in schedules.items():
        current_time = start_time
        available_slots[person] = []
        for block in blocks:
            block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block)
            if current_time < block_start:
                available_slots[person].append((current_time, block_start))
            current_time = max(current_time, block_end)
        if current_time < end_time:
            available_slots[person].append((current_time, end_time))
    
    # Find common available slots
    common_slots = available_slots[next(iter(available_slots))]
    for slots in list(available_slots.values())[1:]:  # Convert dict_values to list
        new_common_slots = []
        for slot1 in common_slots:
            for slot2 in slots:
                overlap_start = max(slot1[0], slot2[0])
                overlap_end = min(slot1[1], slot2[1])
                if overlap_start < overlap_end:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
    
    # Filter slots that are long enough for the meeting
    common_slots = [(start, end) for start, end in common_slots if (end - start).seconds >= meeting_duration * 60]
    
    # Return the earliest common slot
    if common_slots:
        earliest_slot = min(common_slots, key=lambda x: x[0])
        return earliest_slot[0].strftime("%H:%M"), earliest_slot[1].strftime("%H:%M")
    else:
        return None

# Define the schedules
schedules = {
    "Denise": [("12:00", "12:30"), ("15:30", "16:00")],
    "Angela": [],
    "Natalie": [("9:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")]
}

# Meeting duration in hours
meeting_duration = 0.5

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the result
if meeting_start and meeting_end:
    print(f"Meeting can be scheduled from {meeting_start} to {meeting_end} on Monday.")
else:
    print("No common time slot available for the meeting.")