from datetime import datetime, timedelta

def find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, available_days):
    meeting_duration = timedelta(minutes=meeting_duration)
    
    for day in available_days:
        ryan_busy_times = ryan_schedule[day]
        adam_busy_times = adam_schedule[day]
        
        start_of_day = datetime.strptime(f"{day} 09:00", "%A %H:%M")
        end_of_day = datetime.strptime(f"{day} 17:00", "%A %H:%M")
        
        current_time = start_of_day
        
        while current_time + meeting_duration <= end_of_day:
            available_for_ryan = all(current_time < busy_start or current_time + meeting_duration > busy_end for busy_start, busy_end in ryan_busy_times)
            available_for_adam = all(current_time < busy_start or current_time + meeting_duration > busy_end for busy_start, busy_end in adam_busy_times)
            
            if available_for_ryan and available_for_adam:
                return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), day
            
            current_time += timedelta(minutes=15)  # Check every 15 minutes for availability
    
    return None

# Define schedules
ryan_schedule = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

adam_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Constraints
meeting_duration = 30  # in minutes
available_days = ["Monday", "Tuesday"]

# Find a suitable meeting time
meeting_time = find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, available_days)

if meeting_time:
    start_time, end_time, day = meeting_time
    print(f"{start_time}:{end_time} {day}")
else:
    print("No suitable meeting time found.")