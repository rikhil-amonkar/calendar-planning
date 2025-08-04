from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start_time
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        available = True
        for person, busy_times in participants.items():
            for busy_start, busy_end in busy_times:
                busy_start = datetime.strptime(busy_start, "%H:%M")
                busy_end = datetime.strptime(busy_end, "%H:%M")
                if busy_start <= current_time < busy_end or busy_start < current_time + timedelta(minutes=meeting_duration) <= busy_end:
                    available = False
                    break
            if not available:
                break
        if available:
            available_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        current_time += timedelta(minutes=1)
    
    return available_slots

# Participants' busy times
participants = {
    "Jacob": [("13:30", "14:00"), ("14:30", "15:00")],
    "Diana": [("9:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "16:30")],
    "Adam": [("9:30", "10:30"), ("11:00", "12:30"), ("15:30", "16:00")],
    "Angela": [("9:30", "10:00"), ("10:30", "12:00"), ("13:00", "15:30"), ("16:00", "16:30")],
    "Dennis": [("9:00", "9:30"), ("10:30", "11:30"), ("13:00", "15:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
start_time = "9:00"
end_time = "17:00"

# Find available meeting times
available_slots = find_meeting_time(participants, meeting_duration, start_time, end_time)

# Output the first available slot
if available_slots:
    print(f"{available_slots[0][0]}:{available_slots[0][1]}, Monday")
else:
    print("No available time slot found.")