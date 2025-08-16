from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert times to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to hold available slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start_time
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        slot_available = True
        for person_schedule in schedules.values():
            for event_start, event_end in person_schedule:
                event_start = datetime.strptime(event_start, "%H:%M")
                event_end = datetime.strptime(event_end, "%H:%M")
                if current_time < event_end and current_time + timedelta(minutes=meeting_duration) > event_start:
                    slot_available = False
                    break
            if not slot_available:
                break
        if slot_available:
            available_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        current_time += timedelta(minutes=1)
    
    return available_slots[0] if available_slots else None

# Define the schedules
schedules = {
    "Denise": [("12:00", "12:30"), ("15:30", "16:00")],
    "Angela": [],
    "Natalie": [("9:00", "11:30"), ("12:00", "13:00"), ("14:00", "14:30"), ("15:00", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
start_time = "09:00"
end_time = "17:00"

# Find the earliest available meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, start_time, end_time)

if meeting_time:
    print(f"{meeting_time[0]}:{meeting_time[1]} Monday")
else:
    print("No available time found.")