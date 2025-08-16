from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start
    while current_time + timedelta(minutes=duration) <= end:
        # Check if all participants are free at this time
        if all(current_time.strftime("%H:%M") not in busy_times and 
               (current_time + timedelta(minutes=duration)).strftime("%H:%M") not in busy_times
               for busy_times in schedules.values()):
            available_slots.append((current_time, current_time + timedelta(minutes=duration)))
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    if available_slots:
        return available_slots[0]
    else:
        return None

# Define the busy times for each participant
schedules = {
    "Megan": ["09:00", "09:30", "10:00", "11:00", "12:00", "12:30"],
    "Christine": ["09:00", "09:30", "11:30", "12:00", "13:00", "14:00", "15:30", "16:30"],
    "Gabriel": [],
    "Sara": ["11:30", "12:00", "14:30", "15:00"],
    "Bruce": ["09:30", "10:00", "10:30", "12:00", "12:30", "14:00", "14:30", "15:00", "15:30", "16:30"],
    "Kathryn": ["10:00", "15:30", "16:00", "16:30"],
    "Billy": ["09:00", "09:30", "11:00", "11:30", "12:00", "14:00", "14:30", "15:00", "15:30"]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
workday_start = "09:00"
workday_end = "17:00"

# Find a suitable meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, workday_start, workday_end)

if meeting_time:
    start_time, end_time = meeting_time
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday")
else:
    print("No available time found.")