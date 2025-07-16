from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time, day_of_week):
    # Convert start and end times to datetime objects
    start_datetime = datetime.strptime(f"{day_of_week} {start_time}", "%A %H:%M")
    end_datetime = datetime.strptime(f"{day_of_week} {end_time}", "%A %H:%M")
    
    # Initialize a list to store available slots
    available_slots = []
    
    # Iterate over each minute in the day to find available slots
    current_time = start_datetime
    while current_time + timedelta(minutes=meeting_duration) <= end_datetime:
        slot_available = True
        for person, person_schedule in participants.items():
            for busy_start, busy_end in person_schedule:
                busy_start_datetime = datetime.strptime(f"{day_of_week} {busy_start}", "%A %H:%M")
                busy_end_datetime = datetime.strptime(f"{day_of_week} {busy_end}", "%A %H:%M")
                if current_time < busy_end_datetime and current_time + timedelta(minutes=meeting_duration) > busy_start_datetime:
                    slot_available = False
                    break
            if not slot_available:
                break
        if slot_available:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=1)
    
    # Return the first available slot that meets all constraints
    for slot_start, slot_end in available_slots:
        if slot_start.hour >= 14:  # David's constraint
            return f"{slot_start.strftime('%H:%M')}:{slot_end.strftime('%H:%M')}", day_of_week

# Define participants' schedules
participants = {
    "Natalie": [],
    "David": [("11:30", "12:00"), ("14:30", "15:00")],
    "Douglas": [("9:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")],
    "Ralph": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:30"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Jordan": [("9:00", "10:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("15:30", "17:00")]
}

# Meeting details
meeting_duration = 30  # in minutes
start_time = "9:00"
end_time = "17:00"
day_of_week = "Monday"

# Find and print the meeting time
meeting_time, day = find_meeting_time(participants, meeting_duration, start_time, end_time, day_of_week)
print(meeting_time, day)