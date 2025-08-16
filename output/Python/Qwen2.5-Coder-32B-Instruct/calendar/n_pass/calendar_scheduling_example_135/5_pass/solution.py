from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to hold available slots
    available_slots = []

    # Check each minute in the day to find available slots
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        slot_start = current_time
        slot_end = current_time + timedelta(minutes=meeting_duration)
        slot_available = True
        
        # Check if the slot is available for all participants
        for person, person_schedule in schedules.items():
            for busy_start, busy_end in person_schedule:
                busy_start_time = datetime.strptime(busy_start, "%H:%M")
                busy_end_time = datetime.strptime(busy_end, "%H:%M")
                
                # Check if the slot overlaps with any busy time
                if slot_start >= busy_start_time and slot_start < busy_end_time:
                    slot_available = False
                    break
                if slot_end > busy_start_time and slot_end <= busy_end_time:
                    slot_available = False
                    break
                if slot_start < busy_start_time and slot_end > busy_end_time:
                    slot_available = False
                    break
            if not slot_available:
                break
        
        # If the slot is available for all, add it to the list
        if slot_available:
            available_slots.append((slot_start.strftime("%H:%M"), slot_end.strftime("%H:%M")))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    return available_slots[0] if available_slots else None

# Define the schedules for each participant
schedules = {
    "Eric": [],
    "Ashley": [("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00")],
    "Ronald": [("9:00", "9:30"), ("10:00", "11:30"), ("12:30", "14:00"), ("14:30", "17:00")],
    "Larry": [("9:00", "12:00"), ("13:00", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Work hours
start_time = "09:00"
end_time = "17:00"

# Find the meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the result
if meeting_time:
    print(f"{meeting_time[0]}-{meeting_time[1]} Monday")
else:
    print("No available time found.")