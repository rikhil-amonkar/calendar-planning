from datetime import datetime, timedelta

def find_meeting_time(participants, duration, start_time, end_time, preferences):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    duration = timedelta(minutes=duration)
    
    # Initialize available slots
    available_slots = []
    
    # Create a time line from start to end time with 30 minute intervals
    current_time = start_time
    while current_time + duration <= end_time:
        available_slots.append(current_time)
        current_time += timedelta(minutes=30)
    
    # Filter available slots based on participants' schedules
    for person, busy_times in participants.items():
        filtered_slots = []
        for slot in available_slots:
            slot_end = slot + duration
            if all(slot >= busy_end or slot_end <= busy_start for busy_start, busy_end in busy_times):
                filtered_slots.append(slot)
        available_slots = filtered_slots
    
    # Apply preferences
    for preference, value in preferences.items():
        if preference == "avoid_after":
            avoid_after = datetime.strptime(value, "%H:%M")
            available_slots = [slot for slot in available_slots if slot < avoid_after]
    
    # Return the first available slot
    if available_slots:
        meeting_start = available_slots[0]
        meeting_end = meeting_start + duration
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}, Monday"
    else:
        return "No available time found"

# Define participants' schedules
participants = {
    "Lisa": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
             (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Bobby": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
              (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Randy": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Define preferences
preferences = {
    "avoid_after": "15:00"
}

# Find and print the meeting time
print(find_meeting_time(participants, 30, "09:00", "17:00", preferences))