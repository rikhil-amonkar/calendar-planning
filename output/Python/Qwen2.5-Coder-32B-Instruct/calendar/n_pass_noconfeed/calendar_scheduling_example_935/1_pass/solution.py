from datetime import datetime, timedelta

# Define the work hours and meeting duration
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")
meeting_duration = timedelta(minutes=30)

# Define the busy times for each participant
busy_times = {
    "Terry": {
        "Monday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                   (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                   (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                    (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                    (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                      (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                      (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                      (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                      (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Thursday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                     (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                     (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                     (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        "Friday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                   (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                   (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                   (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    },
    "Frances": {
        "Monday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                   (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                   (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                   (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
        "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                    (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                    (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                    (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                    (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
        "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                      (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                      (datetime.strptime("11:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                      (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Thursday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                     (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
        "Friday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                   (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                   (datetime.strptime("13:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                   (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
    }
}

# Function to find free slots
def find_free_slots(busy_times, work_start, work_end, meeting_duration):
    free_slots = {}
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
        current_time = work_start
        free_slots[day] = []
        for start, end in sorted(busy_times["Terry"][day] + busy_times["Frances"][day]):
            if current_time < start:
                free_slots[day].append((current_time, min(end, work_end)))
            current_time = max(current_time, end)
        if current_time < work_end:
            free_slots[day].append((current_time, work_end))
    return free_slots

# Find free slots
free_slots = find_free_slots(busy_times, work_start, work_end, meeting_duration)

# Find a suitable meeting time
for day in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]:
    if day == "Tuesday":
        continue  # Avoid Tuesday as per Frances' preference
    for start, end in free_slots[day]:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} {day}")
            exit()