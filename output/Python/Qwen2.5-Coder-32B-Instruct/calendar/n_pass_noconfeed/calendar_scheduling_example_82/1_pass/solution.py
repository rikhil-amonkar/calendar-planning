from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration):
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert all times to datetime objects for easier manipulation
    for person, slots in schedules.items():
        schedules[person] = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in slots]
    
    # Initialize possible meeting times as the full workday
    possible_times = [(workday_start, workday_end)]
    
    # Iterate over each person's schedule and find overlapping free times
    for person, slots in schedules.items():
        new_possible_times = []
        for start, end in possible_times:
            available_start = start
            for busy_start, busy_end in slots:
                if available_start < busy_start:
                    new_possible_times.append((available_start, min(end, busy_start)))
                available_start = max(available_start, busy_end)
            if available_start < end:
                new_possible_times.append((available_start, end))
        possible_times = new_possible_times
    
    # Find a time slot that fits the meeting duration
    for start, end in possible_times:
        if (end - start) >= timedelta(minutes=meeting_duration):
            return start.strftime("%H:%M"), end.strftime("%H:%M")
    
    return None, None

# Define the schedules for Michael, Eric, and Arthur
schedules = {
    "Michael": [("09:30", "10:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    "Eric": [],
    "Arthur": [("09:00", "12:00"), ("13:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Define the meeting duration in minutes
meeting_duration = 30

# Find a suitable meeting time
start_time, end_time = find_meeting_time(schedules, meeting_duration)

# Output the result
print(f"{start_time}:{end_time} Monday")