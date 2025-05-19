from datetime import datetime, timedelta

# Participants' schedules (occupied time slots)
schedules = {
    "Joan": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
             (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Megan": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Austin": [],
    "Betty": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Judith": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Terry": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Kathryn": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
}

# Meeting constraints
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Function to find an available time slot
def find_meeting_time():
    # Get all occupied time slots
    occupied_slots = []
    for slots in schedules.values():
        occupied_slots.extend(slots)
    
    occupied_slots.sort()  # Sort all occupied time slots

    # Check for available slots within working hours
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        next_time = current_time + meeting_duration
        # Check if the current time slot conflicts with any occupied slots
        conflict = any(start < next_time and current_time < end for start, end in occupied_slots)
        
        if not conflict:
            return current_time.strftime("%H:%M"), next_time.strftime("%H:%M")
        
        # Move to the next available time slot
        current_time += timedelta(minutes=30)  # Increment by 30 minutes

    return None, None

# Proposed meeting time
start_time, end_time = find_meeting_time()
day_of_week = "Monday"

# Output in the required format
if start_time and end_time:
    print(f"{start_time}:{end_time}:{day_of_week}")
else:
    print("No available time found.")