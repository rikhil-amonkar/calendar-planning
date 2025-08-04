from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, start_time, end_time):
    # Convert start and end times to datetime objects
    start = datetime.strptime(start_time, "%H:%M")
    end = datetime.strptime(end_time, "%H:%M")
    
    # Initialize a list to keep track of available slots
    available_slots = []
    
    # Iterate over each minute in the workday
    current_time = start
    while current_time + timedelta(minutes=meeting_duration) <= end:
        slot_available = True
        for person, person_schedule in schedules.items():
            for busy_start, busy_end in person_schedule:
                busy_start_dt = datetime.strptime(busy_start, "%H:%M")
                busy_end_dt = datetime.strptime(busy_end, "%H:%M")
                if busy_start_dt <= current_time < busy_end_dt or busy_start_dt < current_time + timedelta(minutes=meeting_duration) <= busy_end_dt:
                    slot_available = False
                    break
            if not slot_available:
                break
        if slot_available:
            available_slots.append((current_time.strftime("%H:%M"), (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")))
        current_time += timedelta(minutes=1)
    
    return available_slots

# Define the schedules
schedules = {
    "Andrea": [("9:30", "10:30"), ("13:30", "14:30")],
    "Ruth": [("12:30", "13:00"), ("15:00", "15:30")],
    "Steven": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("15:00", "16:00")],
    "Grace": [],
    "Kyle": [("9:00", "9:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Elijah": [("9:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Lori": [("9:00", "9:30"), ("10:00", "11:30"), ("12:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")]
}

# Meeting duration in minutes
meeting_duration = 30

# Workday start and end times
start_time = "09:00"
end_time = "17:00"

# Find available meeting times
available_slots = find_meeting_time(schedules, meeting_duration, start_time, end_time)

# Output the first available slot
if available_slots:
    print(f"{available_slots[0][0]}:{available_slots[0][1]} Monday")
else:
    print("No available time slots found.")