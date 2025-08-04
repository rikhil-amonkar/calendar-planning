from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots for all participants
    common_free_slots = []
    
    # Iterate over each minute in the day to find common free slots
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        is_free_for_all = True
        for person, busy_slots in participants.items():
            for busy_start, busy_end in busy_slots:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    is_free_for_all = False
                    break
            if not is_free_for_all:
                break
        if is_free_for_all:
            common_free_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        current_time += timedelta(minutes=1)
    
    return common_free_slots[0] if common_free_slots else None

# Define participants' busy slots
participants = {
    "Bradley": [("9:30", "10:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00")],
    "Teresa": [("10:30", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Elizabeth": [("9:00", "9:30"), ("10:30", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")],
    "Christian": [("9:00", "9:30"), ("10:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "9:00"
end_time = "17:00"

# Find a suitable meeting time
meeting_time = find_meeting_time(participants, meeting_duration, start_time, end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} Monday")
else:
    print("No common time slot found.")