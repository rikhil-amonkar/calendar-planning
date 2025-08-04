from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    
    # Convert all busy times to datetime objects
    busy_times = []
    for person, times in participants.items():
        person_busy_times = []
        for time_range in times:
            start, end = time_range.split(" to ")
            person_busy_times.append((datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")))
        busy_times.append(person_busy_times)
    
    # Find common free time
    current_time = start_time
    while current_time + timedelta(hours=meeting_duration) <= end_time:
        is_free = True
        for times in busy_times:
            if any(current_time < busy_end and current_time + timedelta(hours=meeting_duration) > busy_start for busy_start, busy_end in times):
                is_free = False
                break
        if is_free:
            return current_time.strftime("%H:%M"), (current_time + timedelta(hours=meeting_duration)).strftime("%H:%M")
        current_time += timedelta(minutes=30)  # Check every 30 minutes
    
    return None

participants = {
    "Stephanie": ["10:00 to 10:30", "16:00 to 16:30"],
    "Cheryl": ["10:00 to 10:30", "11:30 to 12:00", "13:30 to 14:00", "16:30 to 17:00"],
    "Bradley": ["9:30 to 10:00", "10:30 to 11:30", "13:30 to 14:00", "14:30 to 15:00", "15:30 to 17:00"],
    "Steven": ["9:00 to 12:00", "13:00 to 13:30", "14:30 to 17:00"]
}

meeting_duration = 1  # Duration in hours
start, end = find_meeting_time(participants, meeting_duration)
print(f"{start}:{end} Monday")