from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M").time()
work_end = datetime.strptime("17:00", "%H:%M").time()

# Define participants' busy times
bryan_busy = {
    "Thursday": [(datetime.strptime("09:30", "%H:%M").time(), datetime.strptime("10:00", "%H:%M").time()),
                 (datetime.strptime("12:30", "%H:%M").time(), datetime.strptime("13:00", "%H:%M").time())],
    "Friday": [(datetime.strptime("10:30", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
               (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time())]
}

nicholas_busy = {
    "Monday": [(datetime.strptime("11:30", "%H:%M").time(), datetime.strptime("12:00", "%H:%M").time()),
                 (datetime.strptime("13:00", "%H:%M").time(), datetime.strptime("15:30", "%H:%M").time())],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("09:30", "%H:%M").time()),
                  (datetime.strptime("11:00", "%H:%M").time(), datetime.strptime("13:30", "%H:%M").time()),
                  (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("16:30", "%H:%M").time())],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("09:30", "%H:%M").time()),
                    (datetime.strptime("10:00", "%H:%M").time(), datetime.strptime("11:00", "%H:%M").time()),
                    (datetime.strptime("11:30", "%H:%M").time(), datetime.strptime("13:30", "%H:%M").time()),
                    (datetime.strptime("14:00", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time()),
                    (datetime.strptime("15:00", "%H:%M").time(), datetime.strptime("16:30", "%H:%M").time())],
    "Thursday": [(datetime.strptime("10:30", "%H:%M").time(), datetime.strptime("11:30", "%H:%M").time()),
                   (datetime.strptime("12:00", "%H:%M").time(), datetime.strptime("12:30", "%H:%M").time()),
                   (datetime.strptime("15:00", "%H:%M").time(), datetime.strptime("15:30", "%H:%M").time()),
                   (datetime.strptime("16:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())],
    "Friday": [(datetime.strptime("09:00", "%H:%M").time(), datetime.strptime("10:30", "%H:%M").time()),
                 (datetime.strptime("11:00", "%H:%M").time(), datetime.strptime("12:00", "%H:%M").time()),
                 (datetime.strptime("12:30", "%H:%M").time(), datetime.strptime("14:30", "%H:%M").time()),
                 (datetime.strptime("15:30", "%H:%M").time(), datetime.strptime("16:00", "%H:%M").time()),
                 (datetime.strptime("16:30", "%H:%M").time(), datetime.strptime("17:00", "%H:%M").time())]
}

# Define preferences
bryan_avoid_tuesday = True
nicholas_avoid_monday_thursday = True

# Meeting duration
meeting_duration = timedelta(hours=1)

# Function to check if a time slot is free for all participants
def is_slot_free(day, start_time):
    end_time = (datetime.combine(datetime.today(), start_time) + meeting_duration).time()
    
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
    while datetime.combine(datetime.today(), current_time) + meeting_duration <= datetime.combine(datetime.today(), work_end):
        if is_slot_free(day, current_time):
            print(f"{day} {current_time.strftime('%H:%M')}-{(datetime.combine(datetime.today(), current_time) + meeting_duration).time().strftime('%H:%M')}")
            break
        current_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=30)).time()