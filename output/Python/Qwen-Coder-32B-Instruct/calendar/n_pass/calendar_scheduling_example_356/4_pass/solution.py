from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, preferred_end_time):
    start_of_day = datetime.strptime("09:00", "%H:%M")
    end_of_day = datetime.strptime("17:00", "%H:%M")
    lunch_start = datetime.strptime("12:00", "%H:%M")
    lunch_end = datetime.strptime("13:00", "%H:%M")
    
    # Convert all times to datetime objects for easier comparison
    for person, schedule in schedules.items():
        schedules[person] = [(datetime.strptime(start, "%H:%M"), datetime.strptime(end, "%H:%M")) for start, end in schedule]
    
    current_time = start_of_day
    while current_time + timedelta(minutes=duration) <= end_of_day:
        available = True
        for person, schedule in schedules.items():
            if any(current_time < end and current_time + timedelta(minutes=duration) > start for start, end in schedule):
                available = False
                break
        
        # Check if the current time is within the lunch time slot
        if current_time >= lunch_start and current_time < lunch_end:
            available = False
        
        if available:
            if current_time + timedelta(minutes=duration) <= preferred_end_time:
                return current_time.strftime("%H:%M"), (current_time + timedelta(minutes=duration)).strftime("%H:%M"), "Monday"
        
        current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

# Schedules in the format of (start_time, end_time)
schedules = {
    "Katherine": [("12:00", "12:30"), ("13:00", "14:30")],
    "Rebecca": [],
    "Julie": [("9:00", "9:30"), ("10:30", "11:00"), ("13:30", "14:00"), ("15:00", "15:30")],
    "Angela": [("9:00", "10:00"), ("10:30", "11:00"), ("11:30", "14:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Nicholas": [("9:30", "11:00"), ("11:30", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
    "Carl": [("9:00", "11:00"), ("11:30", "12:30"), ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")]
}

preferred_end_time = datetime.strptime("15:00", "%H:%M")
meeting_time = find_meeting_time(schedules, 30, preferred_end_time)

if meeting_time:
    meeting_start, meeting_end, day_of_week = meeting_time
    print(f"Meeting from {meeting_start} to {meeting_end} on {day_of_week}")
else:
    print("No available meeting time found.")