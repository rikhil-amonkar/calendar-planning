from datetime import datetime, timedelta

def find_meeting_time(schedules, duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize available time slots
    available_slots = []
    
    # Check each minute in the range for availability
    current_time = start
    while current_time + timedelta(minutes=duration) <= end:
        slot_available = True
        for person, blocks in schedules.items():
            for block in blocks:
                if current_time >= block[0] and current_time < block[1]:
                    slot_available = False
                    break
            if not slot_available:
                break
        if slot_available:
            available_slots.append((current_time, current_time + timedelta(minutes=duration)))
        current_time += timedelta(minutes=1)
    
    # Return the first available slot
    if available_slots:
        return available_slots[0]
    else:
        return None

# Define the schedules as lists of tuples (start, end) in datetime format
schedules = {
    "Tyler": [],
    "Kelly": [],
    "Stephanie": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Hannah": [],
    "Joe": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
            (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
            (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
            (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Diana": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Deborah": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Meeting duration in minutes
meeting_duration = 30

# Find a suitable meeting time
meeting_time = find_meeting_time(schedules, meeting_duration, "9:00", "17:00")

# Output the result
if meeting_time:
    print(f"{meeting_time[0].strftime('%H:%M')}:{meeting_time[1].strftime('%H:%M')}, Monday")
else:
    print("No available time found.")