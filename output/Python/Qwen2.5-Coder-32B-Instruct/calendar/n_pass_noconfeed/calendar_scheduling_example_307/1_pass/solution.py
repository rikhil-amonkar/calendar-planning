from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available slots for each participant
    available_slots = {name: [] for name in participants}
    
    # Populate available slots for each participant
    for name, blocks in participants.items():
        current = start
        for block in blocks:
            block_start, block_end = map(lambda x: datetime.strptime(x, "%H:%M"), block)
            if current < block_start:
                available_slots[name].append((current, block_start))
            current = max(current, block_end)
        if current < end:
            available_slots[name].append((current, end))
    
    # Find common available slots
    common_slots = []
    for slot in available_slots[next(iter(available_slots))]:
        is_common = True
        for slots in available_slots.values():
            if not any(slot[0] <= s[1] and slot[1] >= s[0] for s in slots):
                is_common = False
                break
        if is_common:
            common_slots.append(slot)
    
    # Find a slot that fits the meeting duration
    for slot in common_slots:
        if (slot[1] - slot[0]).seconds // 60 >= meeting_duration:
            return slot[0].strftime("%H:%M"), slot[0].strftime("%H:%M") + ":" + (slot[0] + timedelta(minutes=meeting_duration)).strftime("%H:%M"), "Monday"
    
    return None

# Participants' schedules
participants = {
    "Ronald": [],
    "Stephen": [("10:00", "10:30"), ("12:00", "12:30")],
    "Brittany": [("11:00", "11:30"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Dorothy": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
    "Rebecca": [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")],
    "Jordan": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("13:00", "15:00"), ("15:30", "16:30")]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find and print the meeting time
meeting_time = find_meeting_time(participants, meeting_duration, start_time, end_time)
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} {meeting_time[2]}")
else:
    print("No common time found")