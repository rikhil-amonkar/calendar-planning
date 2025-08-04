from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define the busy times for each participant
diane_busy_times = {
    "Monday": [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Friday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

matthew_busy_times = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting duration
meeting_duration = timedelta(hours=1)

# Preference for Matthew
matthew_preference = {"Wednesday": datetime.strptime("12:30", "%H:%M")}

def is_time_slot_free(busy_times, start_time, end_time):
    for busy_start, busy_end in busy_times:
        if start_time < busy_end and end_time > busy_start:
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        current_time = work_start
        while current_time + meeting_duration <= work_end:
            diane_busy = diane_busy_times.get(day, [])
            matthew_busy = matthew_busy_times.get(day, [])
            
            # Check if Matthew's preference is respected on Wednesday
            if day == "Wednesday" and current_time < matthew_preference[day]:
                current_time = matthew_preference[day]
                continue
            
            if is_time_slot_free(diane_busy, current_time, current_time + meeting_duration) and \
               is_time_slot_free(matthew_busy, current_time, current_time + meeting_duration):
                return current_time.strftime("%H:%M"), (current_time + meeting_duration).strftime("%H:%M"), day
            current_time += timedelta(minutes=30)  # Check every half hour

meeting_start, meeting_end, meeting_day = find_meeting_time()
print(f"{meeting_start}:{meeting_end} {meeting_day}")