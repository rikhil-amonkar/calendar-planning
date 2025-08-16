from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, work_start, work_end):
    # Convert times to minutes since start of the day for easier calculations
    work_start_minutes = work_start.hour * 60 + work_start.minute
    work_end_minutes = work_end.hour * 60 + work_end.minute
    meeting_duration_minutes = meeting_duration.seconds // 60
    
    # Initialize available time slots
    available_slots = []
    
    # Check each participant's schedule
    for person, busy_times in schedules.items():
        current_time = work_start_minutes
        for start, end in busy_times:
            start_minutes = start.hour * 60 + start.minute
            end_minutes = end.hour * 60 + end.minute
            
            # Add free time slot before the next busy period
            if current_time < start_minutes:
                available_slots.append((current_time, min(end_minutes, work_end_minutes)))
            
            # Update current time to the end of the busy period
            current_time = max(current_time, end_minutes)
        
        # Add free time slot after the last busy period if any
        if current_time < work_end_minutes:
            available_slots.append((current_time, work_end_minutes))
    
    # Find common available time slot
    common_slots = available_slots[0]
    for slot in available_slots[1:]:
        common_slots = (max(common_slots[0], slot[0]), min(common_slots[1], slot[1]))
        if common_slots[0] + meeting_duration_minutes > common_slots[1]:
            common_slots = (0, 0)  # No common slot found
    
    # Convert back to HH:MM format
    if common_slots[0] + meeting_duration_minutes <= common_slots[1]:
        start_time = datetime.strptime(f"{common_slots[0]//60}:{common_slots[0]%60}", "%H:%M")
        end_time = start_time + timedelta(minutes=meeting_duration_minutes)
        return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}, Monday"
    else:
        return "No common time slot found"

# Define the schedules and constraints
schedules = {
    'Andrew': [],
    'Grace': [],
    'Samuel': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
    ]
}

meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Find and print the meeting time
print(find_meeting_time(schedules, meeting_duration, work_start, work_end))