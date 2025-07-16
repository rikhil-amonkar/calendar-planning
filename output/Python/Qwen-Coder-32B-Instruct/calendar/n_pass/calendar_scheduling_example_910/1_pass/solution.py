from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define participants' busy times
bryan_busy = {
    "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M"))],
    "Friday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))]
}

nicholas_busy = {
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

# Define preferences
bryan_avoid_tuesday = True
nicholas_avoid_monday_thursday = True

# Meeting duration
meeting_duration = timedelta(hours=1)

# Function to check if a time slot is free for all participants
def is_slot_free(day, start_time):
    end_time = start_time + meeting_duration
    
    # Check Bryan's availability
    if day in bryan_busy:
        for busy_start, busy_end in bryan_busy[day]:
            if busy_start <= end_time and start_time <= busy_end:
                return False
    
    # Check Nicholas's availability
    if day in nicholas_busy:
        for busy_start, busy_end in nicholas_busy[day]:
            if busy_start <= end_time and start_time <= busy_end:
                return False
    
    return True

# Iterate over possible days and times
for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
    if (day == "Tuesday" and bryan_avoid_tuesday) or (day in ["Monday", "Thursday"] and nicholas_avoid_monday_thursday):
        continue
    
    current_time = work_start
    while current_time + meeting_duration <= work_end:
        if is_slot_free(day, current_time):
            print(f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')} {day}")
            break
        current_time += timedelta(minutes=30)