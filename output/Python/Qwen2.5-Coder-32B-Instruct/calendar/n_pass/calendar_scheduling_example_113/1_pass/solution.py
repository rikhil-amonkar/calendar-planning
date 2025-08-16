from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Initialize available time slots for each participant
    available_slots = {}
    for name, schedule in participants.items():
        current_time = work_start
        slots = []
        for event in schedule:
            event_start, event_end = map(lambda x: datetime.strptime(x, "%H:%M"), event)
            if current_time < event_start:
                slots.append((current_time, event_start))
            current_time = max(current_time, event_end)
        if current_time < work_end:
            slots.append((current_time, work_end))
        available_slots[name] = slots
    
    # Find common available slots
    common_slots = available_slots[next(iter(available_slots))]
    for slots in available_slots.values():
        new_common_slots = []
        for slot1 in common_slots:
            for slot2 in slots:
                overlap_start = max(slot1[0], slot2[0])
                overlap_end = min(slot1[1], slot2[1])
                if overlap_end - overlap_start >= meeting_duration:
                    new_common_slots.append((overlap_start, overlap_start + meeting_duration))
        common_slots = new_common_slots
    
    # Return the first valid slot found
    if common_slots:
        start_time, end_time = common_slots[0]
        return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Participants' schedules
participants = {
    "Bradley": [("09:30", "10:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00")],
    "Teresa": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Elizabeth": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Christian": [("09:00", "09:30"), ("10:30", "17:00")]
}

# Meeting details
meeting_duration = 30
work_start = "09:00"
work_end = "17:00"

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, work_start, work_end)
print(f"{meeting_time}:{day_of_week}")