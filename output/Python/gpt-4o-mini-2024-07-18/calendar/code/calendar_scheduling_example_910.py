from datetime import datetime, timedelta

# Participant schedules
bryan_schedule = {
    "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))],
    "Friday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))]
}

nicholas_schedule = {
    "Monday": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(hours=1)

# Available slots check
def check_availability(day):
    # All work hours
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    
    # Schedule blocks
    bryan_busy = bryan_schedule.get(day, [])
    nicholas_busy = nicholas_schedule.get(day, [])
    
    busy_times = bryan_busy + nicholas_busy
    busy_times.sort()  # Sort by start time
    
    current_time = work_start
    
    while current_time + meeting_duration <= work_end:
        # Check if the current time is busy
        is_busy = any(start <= current_time < end for start, end in busy_times)
        
        if not is_busy:
            # Check if the meeting duration fits in this slot
            if not any(start < current_time + meeting_duration <= end for start, end in busy_times):
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} - {day}"
        
        # Move to the next minute
        current_time += timedelta(minutes=1)

# Checking available days
for day in ["Tuesday", "Wednesday", "Thursday", "Friday"]:
    proposed_time = check_availability(day)
    if proposed_time:
        print(proposed_time)
        break