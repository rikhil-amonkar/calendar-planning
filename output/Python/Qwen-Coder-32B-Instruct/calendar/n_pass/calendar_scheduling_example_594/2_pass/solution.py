from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to datetime objects for easier manipulation
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)
    
    # Function to convert time string to datetime object
    def time_to_datetime(time_str):
        return datetime.strptime(time_str, "%H:%M")
    
    # Function to convert datetime object back to time string
    def datetime_to_time(dt):
        return dt.strftime("%H:%M")
    
    # Initialize available slots for each person
    available_slots = {}
    
    # Check each person's schedule
    for person, schedule in schedules.items():
        current_time = work_start
        person_slots = []
        for busy_start, busy_end in schedule:
            busy_start = time_to_datetime(busy_start)
            busy_end = time_to_datetime(busy_end)
            
            # Add free time slot before the next busy period
            if current_time < busy_start:
                person_slots.append((current_time, busy_start))
            
            # Update current time to after the busy period
            current_time = max(current_time, busy_end)
        
        # Add free time slot after the last busy period until work end
        if current_time < work_end:
            person_slots.append((current_time, work_end))
        
        available_slots[person] = person_slots
    
    # Find common free slots
    common_slots = available_slots[list(available_slots.keys())[0]]
    
    for person, slots in available_slots.items():
        new_common_slots = []
        for common_start, common_end in common_slots:
            for slot_start, slot_end in slots:
                overlap_start = max(common_start, slot_start)
                overlap_end = min(common_end, slot_end)
                if overlap_start + meeting_duration <= overlap_end:
                    new_common_slots.append((overlap_start, overlap_end))
        common_slots = new_common_slots
    
    # Return the first valid common slot found
    if common_slots:
        return datetime_to_time(common_slots[0][0]), datetime_to_time(common_slots[0][1])
    
    return None, None

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
if start_time and end_time:
    print(f"Meeting time: {start_time} - {end_time} on {day_of_week}")
else:
    print("No suitable meeting time found.")