from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, preferred_start=None):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Convert all times to datetime objects for easier comparison
    for person, schedule in schedules.items():
        schedules[person] = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in schedule]
    
    # Sort schedules by start time
    for person in schedules:
        schedules[person].sort()
    
    # Find common free slots
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        available = True
        for person, schedule in schedules.items():
            for start, end in schedule:
                if start <= current_time < end or start < current_time + meeting_duration <= end:
                    available = False
                    break
            if not available:
                break
        if available:
            if preferred_start and current_time < preferred_start:
                current_time += timedelta(minutes=30)
                continue
            return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", "Monday"
        current_time += timedelta(minutes=30)
    
    return None

# Define the schedules
schedules = {
    'Kimberly': [('10:00', '10:30'), ('11:00', '12:00'), ('16:00', '16:30')],
    'Megan': [],
    'Marie': [('10:00', '11:00'), ('11:30', '15:00'), ('16:00', '16:30')],
    'Diana': [('09:30', '10:00'), ('10:30', '14:30'), ('15:30', '17:00')]
}

# Preferred start time for Megan
preferred_start = datetime.strptime("10:00", "%H:%M")

# Find and print the meeting time
meeting_time, day = find_meeting_time(schedules, 30, preferred_start)
print(f"{meeting_time}, {day}")