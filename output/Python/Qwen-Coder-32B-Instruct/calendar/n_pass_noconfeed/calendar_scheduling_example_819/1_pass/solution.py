from datetime import datetime, timedelta

# Define the work hours and constraints
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the schedules
julie_schedule = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": []
}

ruth_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to find available slots
def find_available_slots(schedule, work_start, work_end, meeting_duration):
    available_slots = []
    current_time = work_start
    
    for start, end in schedule:
        if current_time < start:
            while current_time + meeting_duration <= start:
                available_slots.append((current_time, current_time + meeting_duration))
                current_time += meeting_duration
        current_time = max(current_time, end)
    
    if current_time + meeting_duration <= work_end:
        while current_time + meeting_duration <= work_end:
            available_slots.append((current_time, current_time + meeting_duration))
            current_time += meeting_duration
    
    return available_slots

# Find common slots
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    julie_slots = find_available_slots(julie_schedule[day], work_start, work_end, meeting_duration)
    ruth_slots = find_available_slots(ruth_schedule[day], work_start, work_end, meeting_duration)
    
    common_slots = [slot for slot in julie_slots if slot in ruth_slots]
    
    # Filter out slots before 11:30 on Thursday
    if day == "Thursday":
        common_slots = [slot for slot in common_slots if slot[0] >= datetime.strptime("11:30", "%H:%M")]
    
    if common_slots:
        # Output the first available slot
        start_time, end_time = common_slots[0]
        print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")
        break