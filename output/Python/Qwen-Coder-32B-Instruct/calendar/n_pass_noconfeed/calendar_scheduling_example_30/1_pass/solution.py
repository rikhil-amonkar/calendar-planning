from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, preferred_end_time):
    # Define the workday start and end times
    workday_start = datetime.strptime("09:00", "%H:%M")
    workday_end = datetime.strptime("17:00", "%H:%M")
    
    # Convert preferred end time to datetime object
    preferred_end_time = datetime.strptime(preferred_end_time, "%H:%M")
    
    # Initialize a list to store available time slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = workday_start
    while current_time + timedelta(minutes=meeting_duration) <= workday_end:
        # Check if the current time slot is available for all participants
        slot_available = True
        for person_schedule in schedules.values():
            for busy_start, busy_end in person_schedule:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    slot_available = False
                    break
            if not slot_available:
                break
        
        # If the slot is available, add it to the list
        if slot_available:
            available_slots.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        
        # Move to the next minute
        current_time += timedelta(minutes=1)
    
    # Filter slots based on the preferred end time
    filtered_slots = [(start, end) for start, end in available_slots if end <= preferred_end_time]
    
    # Return the first available slot that meets the criteria
    if filtered_slots:
        start_time, end_time = filtered_slots[0]
        return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday"
    else:
        return "No available time slot found"

# Define the schedules for each participant
schedules = {
    "Jeffrey": [("09:30", "10:00"), ("10:30", "11:00")],
    "Virginia": [("09:00", "09:30"), ("10:00", "10:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Melissa": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("16:00", "17:00")]
}

# Define the meeting duration and preferred end time
meeting_duration = 30  # in minutes
preferred_end_time = "14:00"

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, preferred_end_time))