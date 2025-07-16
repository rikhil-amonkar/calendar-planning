from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Initialize available slots
    available_slots = []
    
    # Check each person's schedule
    for person, schedule in schedules.items():
        current_time = work_start
        for busy_start, busy_end in schedule:
            busy_start = datetime.strptime(busy_start, "%H:%M")
            busy_end = datetime.strptime(busy_end, "%H:%M")
            
            # Add free time slot before the next busy period
            if current_time < busy_start:
                available_slots.append((current_time, busy_start))
            
            # Update current time to after the busy period
            current_time = max(current_time, busy_end)
        
        # Add free time slot after the last busy period until work end
        if current_time < work_end:
            available_slots.append((current_time, work_end))
    
    # Find common free slots
    common_slots = available_slots[0]
    for slot in available_slots[1:]:
        common_start = max(common_slots[0], slot[0])
        common_end = min(common_slots[1], slot[1])
        if common_start + meeting_duration <= common_end:
            return common_start.strftime("%H:%M"), common_end.strftime("%H:%M")
        else:
            common_slots = slot
    
    return None

# Define the schedules
schedules = {
    "Adam": [("09:30", "10:00"), ("12:30", "13:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Roy": [("10:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("16:30", "17:00")]
}

# Meeting details
meeting_duration = 30  # in minutes
work_start = "09:00"
work_end = "17:00"
day_of_week = "Monday"

# Find a suitable meeting time
start_time, end_time = find_meeting_time(schedules, meeting_duration, work_start, work_end)

# Output the result
print(f"{start_time}:{end_time} {day_of_week}")