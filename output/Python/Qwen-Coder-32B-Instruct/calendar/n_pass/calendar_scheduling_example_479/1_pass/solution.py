from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(f"Monday {start_time}", "%A %H:%M")
    end = datetime.strptime(f"Monday {end_time}", "%A %H:%M")
    
    # Initialize a list to store available slots
    available_slots = []

    # Iterate over each minute in the day to find common free slots
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        is_free_for_all = True
        for person, busy_times in participants.items():
            for busy_start, busy_end in busy_times:
                busy_start_dt = datetime.strptime(f"Monday {busy_start}", "%A %H:%M")
                busy_end_dt = datetime.strptime(f"Monday {busy_end}", "%A %H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    is_free_for_all = False
                    break
            if not is_free_for_all:
                break
        if is_free_for_all:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=1)

    # Return the first available slot found
    if available_slots:
        meeting_start, meeting_end = available_slots[0]
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}, Monday"
    else:
        return "No available time slot found"

# Define participants' busy times
participants = {
    "Evelyn": [],
    "Joshua": [("11:00", "12:30"), ("13:30", "14:30"), ("16:30", "17:00")],
    "Kevin": [],
    "Gerald": [],
    "Jerry": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00")],
    "Jesse": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("15:30", "16:30")],
    "Kenneth": [("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 60

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find and print the meeting time
print(find_meeting_time(participants, meeting_duration, start_time, end_time))