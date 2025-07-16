from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the schedules
susan_schedule = {
    "Monday": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

sandra_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Constraints
susan_avoid_tuesday = True
sandra_avoid_monday_after_16 = True

def find_free_slot(day):
    susan_busy = susan_schedule[day]
    sandra_busy = sandra_schedule[day]
    
    # Combine all busy slots
    all_busy_slots = sorted(susan_busy + sandra_busy)
    
    # Initialize start time
    current_time = work_start
    
    for start, end in all_busy_slots:
        if current_time < start and current_time + meeting_duration <= start:
            return current_time, current_time + meeting_duration
        current_time = max(current_time, end)
    
    if current_time + meeting_duration <= work_end:
        return current_time, current_time + meeting_duration
    
    return None, None

# Check each day for a free slot
for day in ["Monday", "Tuesday", "Wednesday"]:
    if day == "Tuesday" and susan_avoid_tuesday:
        continue
    if day == "Monday":
        # Check if Sandra can meet before 16:00
        free_start, free_end = find_free_slot(day)
        if free_start and free_start < datetime.strptime("16:00", "%H:%M"):
            print(f"{free_start.strftime('%H:%M')}:{free_end.strftime('%H:%M')},{day}")
            break
    else:
        free_start, free_end = find_free_slot(day)
        if free_start:
            print(f"{free_start.strftime('%H:%M')}:{free_end.strftime('%H:%M')},{day}")
            break