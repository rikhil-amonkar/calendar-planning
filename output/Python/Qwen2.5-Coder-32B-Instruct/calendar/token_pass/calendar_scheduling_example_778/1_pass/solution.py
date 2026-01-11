from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define schedules
susan_schedule = {
    'Monday': [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

sandra_schedule = {
    'Monday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    'Tuesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(minutes=30)

# Function to find free slots
def find_free_slots(schedule, day):
    busy_slots = schedule[day]
    free_slots = []
    current_time = work_start
    
    for start, end in busy_slots:
        if current_time < start:
            free_slots.append((current_time, start))
        current_time = max(current_time, end)
    
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    
    return free_slots

# Check each day
for day in ['Monday', 'Tuesday', 'Wednesday']:
    # Skip Tuesday due to Susan's preference
    if day == 'Tuesday':
        continue
    
    susan_free_slots = find_free_slots(susan_schedule, day)
    sandra_free_slots = find_free_slots(sandra_schedule, day)
    
    # Apply Sandra's constraint for Monday
    if day == 'Monday':
        sandra_free_slots = [(start, end) for start, end in sandra_free_slots if end <= datetime.strptime("16:00", "%H:%M")]
    
    # Find common free slots
    for susan_slot in susan_free_slots:
        for sandra_slot in sandra_free_slots:
            common_start = max(susan_slot[0], sandra_slot[0])
            common_end = min(susan_slot[1], sandra_slot[1])
            
            if common_end - common_start >= meeting_duration:
                # Found a valid slot
                start_time_str = common_start.strftime("%H:%M")
                end_time_str = (common_start + meeting_duration).strftime("%H:%M")
                print(f"{start_time_str}:{end_time_str} {day}")
                exit(0)