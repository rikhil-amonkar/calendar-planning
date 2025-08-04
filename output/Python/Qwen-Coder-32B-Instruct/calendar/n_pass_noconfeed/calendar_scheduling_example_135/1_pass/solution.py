from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available slots for each participant
    available_slots = {name: [] for name in participants}
    
    # Populate available slots for each participant
    for name, schedule in participants.items():
        current_time = start_time
        for event_start, event_end in schedule:
            event_start = datetime.strptime(event_start, "%H:%M")
            event_end = datetime.strptime(event_end, "%H:%M")
            
            if current_time < event_start:
                available_slots[name].append((current_time, event_start))
            
            current_time = max(current_time, event_end)
        
        if current_time < end_time:
            available_slots[name].append((current_time, end_time))
    
    # Find common available slots
    common_slots = []
    for slot in available_slots[list(available_slots.keys())[0]]:
        common_slot_start, common_slot_end = slot
        for name in list(available_slots.keys())[1:]:
            found_overlap = False
            for slot in available_slots[name]:
                slot_start, slot_end = slot
                overlap_start = max(common_slot_start, slot_start)
                overlap_end = min(common_slot_end, slot_end)
                if (overlap_end - overlap_start).seconds >= meeting_duration.total_seconds():
                    common_slot_start, common_slot_end = overlap_start, overlap_end
                    found_overlap = True
                    break
            if not found_overlap:
                break
        else:
            common_slots.append((common_slot_start, common_slot_end))
    
    # Return the first valid common slot
    if common_slots:
        start, end = common_slots[0]
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Define participants' schedules
participants = {
    "Eric": [],
    "Ashley": [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],
    "Ronald": [("9:00", "9:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],
    "Larry": [("9:00", "12:00"), ("13:00", "17:00")]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Work hours
start_time = "9:00"
end_time = "17:00"

# Find a suitable meeting time
meeting_time, day_of_week = find_meeting_time(participants, meeting_duration, start_time, end_time)
print(f"{meeting_time}:{day_of_week}")