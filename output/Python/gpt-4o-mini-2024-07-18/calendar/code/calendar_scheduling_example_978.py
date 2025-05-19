from datetime import datetime, timedelta

# Define busy schedules
brian_schedule = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

julia_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                 (datetime.strptime("11:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(hours=1)
work_hours_start = datetime.strptime("09:00", "%H:%M")
work_hours_end = datetime.strptime("17:00", "%H:%M")

# Function to find available slot
def find_available_slot():
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        busy_times = brian_schedule[day] + julia_schedule[day]
        busy_times.sort()
        
        last_end_time = work_hours_start
        
        for busy_start, busy_end in busy_times:
            if last_end_time + meeting_duration <= busy_start:
                return f"{last_end_time.strftime('%H:%M')}:{(last_end_time + meeting_duration).strftime('%H:%M')} on {day}"
            last_end_time = max(last_end_time, busy_end)
        
        # Check after the last busy time
        if last_end_time + meeting_duration <= work_hours_end:
            return f"{last_end_time.strftime('%H:%M')}:{(last_end_time + meeting_duration).strftime('%H:%M')} on {day}"

# Get the proposed time
proposed_time = find_available_slot()
print(proposed_time)