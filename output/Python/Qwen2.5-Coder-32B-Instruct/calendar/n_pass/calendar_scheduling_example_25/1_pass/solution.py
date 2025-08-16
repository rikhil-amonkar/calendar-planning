from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, day, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(f"{day} {work_start}", "%A %H:%M")
    work_end = datetime.strptime(f"{day} {work_end}", "%A %H:%M")
    
    # Parse busy times for each participant
    busy_times = {}
    for name, schedule in participants.items():
        busy_times[name] = [tuple(datetime.strptime(f"{day} {time}", "%A %H:%M") for time in slot.split(" to ")) for slot in schedule]
    
    # Find common free time slots
    current_time = work_start
    while current_time + timedelta(hours=meeting_duration) <= work_end:
        if all(current_time < busy[0] or current_time + timedelta(hours=meeting_duration) > busy[1] for busy_slots in busy_times.values() for busy in busy_slots):
            return current_time.strftime("%H:%M"), (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M"), day
        current_time += timedelta(minutes=15)  # Check every 15 minutes for more granular results
    
    return None

# Participants' schedules
participants = {
    "Anthony": ["9:30 to 10:00", "12:00 to 13:00", "16:00 to 16:30"],
    "Pamela": ["9:30 to 10:00", "16:30 to 17:00"],
    "Zachary": ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 13:30", "14:30 to 15:00", "16:00 to 17:00"]
}

# Meeting details
meeting_duration = 1  # in hours
day = "Monday"
work_start = "9:00"
work_end = "17:00"

# Find and print the meeting time
start_time, end_time, meeting_day = find_meeting_time(participants, meeting_duration, day, work_start, work_end)
print(f"{start_time}:{end_time} {meeting_day}")