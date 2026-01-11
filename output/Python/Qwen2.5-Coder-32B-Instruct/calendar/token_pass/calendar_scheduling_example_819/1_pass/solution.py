from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Ruth's busy times
ruth_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

# Function to find free slots
def find_free_slots(busy_times, work_start, work_end, meeting_duration):
    free_slots = []
    current_time = work_start
    
    for start, end in busy_times:
        if current_time < start:
            if current_time + meeting_duration <= start:
                free_slots.append((current_time, current_time + meeting_duration))
        current_time = max(current_time, end)
    
    if current_time + meeting_duration <= work_end:
        free_slots.append((current_time, current_time + meeting_duration))
    
    return free_slots

# Iterate over days to find a suitable slot
for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
    busy_times = ruth_busy_times[day]
    free_slots = find_free_slots(busy_times, work_start, work_end, meeting_duration)
    
    for start, end in free_slots:
        # Check Julie's preference for Thursday
        if day == "Thursday" and start < datetime.strptime("11:30", "%H:%M"):
            continue
        # Format the output
        print(f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')} {day}")
        break