from datetime import datetime, time, timedelta

# Define work hours
work_start = time(9, 0)
work_end = time(17, 0)

# Define participants' busy times
bryan_busy = {
    "Thursday": [(time(9, 30), time(10, 0)),
                 (time(12, 30), time(13, 0))],
    "Friday": [(time(10, 30), time(11, 0)),
               (time(14, 0), time(14, 30))]
}

nicholas_busy = {
    "Monday": [(time(11, 30), time(12, 0)),
                 (time(13, 0), time(15, 30))],
    "Tuesday": [(time(9, 0), time(9, 30)),
                  (time(11, 0), time(13, 30)),
                  (time(14, 0), time(16, 30))],
    "Wednesday": [(time(9, 0), time(9, 30)),
                    (time(10, 0), time(11, 0)),
                    (time(11, 30), time(13, 30)),
                    (time(14, 0), time(14, 30)),
                    (time(15, 0), time(16, 30)),
                    (time(17, 0), time(24, 0))],  # Added unavailable time from 17:00 to 24:00
    "Thursday": [(time(10, 30), time(11, 30)),
                   (time(12, 0), time(12, 30)),
                   (time(15, 0), time(15, 30)),
                   (time(16, 30), time(17, 0))],
    "Friday": [(time(9, 0), time(10, 30)),
                 (time(11, 0), time(12, 0)),
                 (time(12, 30), time(14, 30)),
                 (time(15, 30), time(16, 0)),
                 (time(16, 30), time(17, 0))]
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
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    
    # Check Nicholas's availability
    if day in nicholas_busy:
        for busy_start, busy_end in nicholas_busy[day]:
            if not (end_time <= busy_start or start_time >= busy_end):
                return False
    
    return True

# Iterate over possible days and times
found_meeting = False
for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
    if (day == "Tuesday" and bryan_avoid_tuesday) or (day in ["Monday", "Thursday"] and nicholas_avoid_monday_thursday):
        continue
    
    current_time = work_start
    while current_time < work_end:
        if is_slot_free(day, current_time):
            print(f"{day} {current_time.strftime('%H:%M')}-{(datetime.combine(datetime.today(), current_time) + meeting_duration).time().strftime('%H:%M')}")
            found_meeting = True
            break
        current_time = (datetime.combine(datetime.today(), current_time) + timedelta(minutes=30)).time()
    
    if found_meeting:
        break

if not found_meeting:
    print("No available meeting time found.")