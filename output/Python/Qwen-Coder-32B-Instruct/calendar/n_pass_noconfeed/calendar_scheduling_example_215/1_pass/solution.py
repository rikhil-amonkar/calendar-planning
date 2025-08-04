from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime("17:00", "%H:%M")
    
    # Initialize a list to store available time slots
    available_slots = []
    
    # Iterate over each minute in the workday to find common free slots
    current_time = workday_start
    while current_time + timedelta(minutes=meeting_duration) <= workday_end:
        is_free_for_all = True
        for person, busy_times in participants.items():
            for busy_start, busy_end in busy_times:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    is_free_for_all = False
                    break
            if not is_free_for_all:
                break
        if is_free_for_all:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=1)
    
    # Return the earliest available slot
    if available_slots:
        start, end = available_slots[0]
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}", "Monday"
    else:
        return None, None

# Define the participants' busy times
participants = {
    "Cynthia": [("09:30", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "16:00")],
    "Lauren": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Robert": [("10:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "16:00")]
}

# Find and print the meeting time
meeting_time, day_of_week = find_meeting_time(participants, 30)
print(f"{meeting_time},{day_of_week}")