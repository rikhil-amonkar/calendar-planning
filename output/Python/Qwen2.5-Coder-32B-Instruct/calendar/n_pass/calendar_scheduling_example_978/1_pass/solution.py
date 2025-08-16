from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy times for Brian and Julia
brian_busy = {
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

julia_busy = {
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

def find_free_slot(day):
    brian_slots = get_free_slots(brian_busy[day], work_start, work_end)
    julia_slots = get_free_slots(julia_busy[day], work_start, work_end)
    return find_common_slot(brian_slots, julia_slots)

def get_free_slots(busy_times, start, end):
    free_slots = []
    current_start = start
    for busy_start, busy_end in busy_times:
        if current_start < busy_start:
            free_slots.append((current_start, busy_start))
        current_start = busy_end
    if current_start < end:
        free_slots.append((current_start, end))
    return free_slots

def find_common_slot(slots1, slots2):
    for start1, end1 in slots1:
        for start2, end2 in slots2:
            common_start = max(start1, start2)
            common_end = min(end1, end2)
            if common_start < common_end and (common_end - common_start) >= timedelta(hours=1):
                return common_start.strftime("%H:%M"), common_end.strftime("%H:%M")
    return None

days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
for day in days_of_week:
    slot = find_free_slot(day)
    if slot:
        print(f"{slot[0]}:{slot[1]} {day}")
        break