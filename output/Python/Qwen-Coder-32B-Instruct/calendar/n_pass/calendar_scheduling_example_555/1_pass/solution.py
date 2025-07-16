from datetime import datetime, timedelta

def find_meeting_time(evelyn_schedule, randy_schedule, evelyn_preference_end, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    evelyn_preference_end = datetime.strptime(evelyn_preference_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Convert string times to datetime objects for easier comparison
    randy_blocked_times = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in randy_schedule]
    
    # Check for available time slots
    current_time = work_start
    while current_time + meeting_duration <= min(work_end, evelyn_preference_end):
        available = True
        for start, end in randy_blocked_times:
            if current_time < end and current_time + meeting_duration > start:
                available = False
                current_time = end
                break
        if available:
            return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M")
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

# Define schedules and preferences
evelyn_schedule = []  # No meetings all day
randy_schedule = [("09:00", "10:30"), ("11:00", "15:30"), ("16:00", "17:00")]
evelyn_preference_end = "13:00"
meeting_duration = 30  # Half an hour

# Find a suitable meeting time
start_time, end_time = find_meeting_time(evelyn_schedule, randy_schedule, evelyn_preference_end, meeting_duration)

# Output the result
print(f"{start_time}:{end_time} Monday")