from datetime import datetime, timedelta

# Define the workday
start_of_day = datetime.strptime("09:00", "%H:%M")
end_of_day = datetime.strptime("17:00", "%H:%M")

# Define the participants' schedules
schedules = {
    "Andrea": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    "Ruth": [(datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
              (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Steven": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Grace": [],
    "Kyle": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
             (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
             (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
             (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
             (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Elijah": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Lori": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
             (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
             (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to check if a time is free for all participants
def is_time_free(time, schedules):
    for person, busy_slots in schedules.items():
        for start, end in busy_slots:
            if start <= time < end:
                return False
    return True

# Find a suitable time slot
meeting_duration = timedelta(minutes=30)
current_time = start_of_day

while current_time + meeting_duration <= end_of_day:
    if is_time_free(current_time, schedules):
        meeting_start = current_time.strftime("%H:%M")
        meeting_end = (current_time + meeting_duration).strftime("%H:%M")
        print(f"{meeting_start}:{meeting_end} Monday")
        break
    current_time += timedelta(minutes=1)