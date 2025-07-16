from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy times for Daniel and Bradley
daniel_busy = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

bradley_busy = {
    "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

# Define constraints
constraints = {
    "Daniel": ["Wednesday", "Thursday"],
    "Bradley": ["Monday", "Friday"]
}
bradley_avoid_before = datetime.strptime("12:00", "%H:%M")

# Meeting duration
meeting_duration = timedelta(minutes=30)

def is_time_slot_free(busy_times, start_time, end_time):
    for busy_start, busy_end in busy_times:
        if start_time < busy_end and end_time > busy_start:
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        if day in constraints["Daniel"] or day in constraints["Bradley"]:
            continue
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            if is_time_slot_free(daniel_busy[day], current_time, current_time + meeting_duration) and \
               is_time_slot_free(bradley_busy[day], current_time, current_time + meeting_duration) and \
               (day != "Tuesday" or current_time >= bradley_avoid_before):
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            current_time += timedelta(minutes=30)
    return None, None

meeting_time, meeting_day = find_meeting_time()
if meeting_time and meeting_day:
    print(f"{meeting_time}:{meeting_day}")
else:
    print("No suitable meeting time found.")