from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert times to datetime objects for easier manipulation
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Check each minute in the day to find available slots
    current_time = start_time
    while current_time + timedelta(minutes=meeting_duration) <= end_time:
        slot_available = True
        for person_schedule in schedules.values():
            for meeting_start, meeting_end in person_schedule:
                meeting_start_dt = datetime.strptime(meeting_start, "%H:%M")
                meeting_end_dt = datetime.strptime(meeting_end, "%H:%M")
                if meeting_start_dt <= current_time < meeting_end_dt or meeting_start_dt < current_time + timedelta(minutes=meeting_duration) <= meeting_end_dt:
                    slot_available = False
                    break
            if not slot_available:
                break
        if slot_available:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=1)
    
    # Return the first available slot found
    if available_slots:
        meeting_start, meeting_end = available_slots[0]
        return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}, Monday"
    else:
        return "No available time slot found"

# Define the schedules for each participant
schedules = {
    "Michael": [("09:30", "10:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    "Eric": [],
    "Arthur": [("09:00", "12:00"), ("13:00", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Define the work hours
start_time = "09:00"
end_time = "17:00"

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, start_time, end_time))