from datetime import datetime, timedelta

# Define the meeting duration
meeting_duration = timedelta(minutes=30)

# Define the available days and work hours
available_days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
work_start_time = datetime.strptime("09:00", "%H:%M")
work_end_time = datetime.strptime("17:00", "%H:%M")

# Define the schedules for Mary and Alexis
mary_schedule = {
    "Tuesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Thursday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M"))]
}

alexis_schedule = {
    "Monday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Thursday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                 (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Function to find free slots
def find_free_slots(schedule, start_time, end_time):
    current_time = start_time
    free_slots = []
    while current_time < end_time:
        next_slot = current_time + meeting_duration
        if next_slot > end_time:
            break
        is_free = True
        for busy_start, busy_end in schedule:
            if not (next_slot <= busy_start or current_time >= busy_end):
                is_free = False
                current_time = busy_end
                break
        if is_free:
            free_slots.append((current_time, next_slot))
            current_time = next_slot
        else:
            current_time += timedelta(minutes=1)
    return free_slots

# Find a common free slot
for day in available_days:
    mary_free_slots = find_free_slots(mary_schedule.get(day, []), work_start_time, work_end_time)
    alexis_free_slots = find_free_slots(alexis_schedule.get(day, []), work_start_time, work_end_time)
    
    for mary_slot in mary_free_slots:
        for alexis_slot in alexis_free_slots:
            if not (mary_slot[1] <= alexis_slot[0] or mary_slot[0] >= alexis_slot[1]):
                # Found a common slot
                meeting_start = max(mary_slot[0], alexis_slot[0])
                meeting_end = meeting_start + meeting_duration
                print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}, {day}")
                exit()