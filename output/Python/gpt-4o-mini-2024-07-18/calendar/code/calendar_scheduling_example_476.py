from datetime import datetime, timedelta

# Define participants' busy times
busy_times = {
    'Kathleen': [(datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    'Carolyn': [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"))],
    'Cheryl': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Virginia': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                 (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Angela': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
}

# Meeting constraints
meeting_duration = timedelta(minutes=30)
working_hours_start = datetime.strptime("09:00", "%H:%M")
working_hours_end = datetime.strptime("17:00", "%H:%M")
roger_pref_start_time = datetime.strptime("12:30", "%H:%M")

# Function to find free time slots
def find_free_time_slots(busy_times):
    busy_slots = []

    for times in busy_times.values():
        busy_slots.extend(times)

    busy_slots.sort()

    free_slots = []
    last_end_time = working_hours_start

    for start, end in busy_slots:
        if last_end_time < start:
            free_slots.append((last_end_time, start))
        last_end_time = max(last_end_time, end)

    if last_end_time < working_hours_end:
        free_slots.append((last_end_time, working_hours_end))

    return free_slots

# Find free time slots for the group
free_slots = find_free_time_slots(busy_times)

# Find a suitable time slot for the meeting
for start, end in free_slots:
    if start >= roger_pref_start_time and (end - start) >= meeting_duration:
        meeting_start_time = start
        meeting_end_time = start + meeting_duration
        break

# Output the meeting time and day
day_of_week = "Monday"
print(f"{meeting_start_time.strftime('%H:%M')}:{meeting_end_time.strftime('%H:%M')}, {day_of_week}")