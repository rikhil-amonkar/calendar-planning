from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_start, work_end):
    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each participant's schedule
    for participant, schedule in participants.items():
        current_time = work_start
        for event in schedule:
            event_start, event_end = map(lambda x: datetime.strptime(x, "%H:%M"), event)
            
            # Check if there's a gap between current time and the start of the next event
            if current_time < event_start:
                available_slots.append((current_time, event_start))
            
            # Update current time to the end of the current event
            current_time = max(current_time, event_end)
        
        # Check if there's a gap between the last event and the end of the work day
        if current_time < work_end:
            available_slots.append((current_time, work_end))
    
    # Find common available slots
    common_slots = available_slots[::]
    for slot in available_slots:
        for participant, schedule in participants.items():
            for event in schedule:
                event_start, event_end = map(lambda x: datetime.strptime(x, "%H:%M"), event)
                if slot[0] < event_end and slot[1] > event_start:
                    if slot in common_slots:
                        common_slots.remove(slot)
                    break
    
    # Find a slot that fits the meeting duration
    for slot in common_slots:
        if (slot[1] - slot[0]).seconds // 3600 >= meeting_duration:
            return slot[0].strftime("%H:%M"), (slot[0] + timedelta(hours=meeting_duration)).strftime("%H:%M")
    
    return None

# Define participants' schedules
participants = {
    "Christine": [("11:00", "11:30"), ("15:00", "15:30")],
    "Helen": [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")]
}

# Meeting details
meeting_duration = 0.5  # in hours
work_start = "09:00"
work_end = "17:00"

# Find a suitable meeting time
start_time, end_time = find_meeting_time(participants, meeting_duration, work_start, work_end)

# Output the result
print(f"{start_time}:{end_time} Monday")