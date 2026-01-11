from datetime import datetime, timedelta

# Define the work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Define busy times for Robert and Ralph
robert_busy = {
    "Monday": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

ralph_busy = {
    "Monday": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Tuesday": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Wednesday": [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                  (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

def find_available_slots(busy_times):
    available_slots = []
    current_time = work_start
    for start, end in busy_times:
        if current_time < start:
            available_slots.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        available_slots.append((current_time, work_end))
    return available_slots

def find_common_slot(available_slots1, available_slots2):
    for start1, end1 in available_slots1:
        for start2, end2 in available_slots2:
            common_start = max(start1, start2)
            common_end = min(end1, end2)
            if (common_end - common_start) >= timedelta(minutes=30):
                return common_start, common_start + timedelta(minutes=30)
    return None

# Days in order of preference
days = ["Tuesday", "Wednesday", "Monday"]

for day in days:
    robert_slots = find_available_slots(robert_busy[day])
    ralph_slots = find_available_slots(ralph_busy[day])
    slot = find_common_slot(robert_slots, ralph_slots)
    if slot:
        print(f"{slot[0].strftime('%H:%M')}:{slot[1].strftime('%H:%M')} {day}")
        break