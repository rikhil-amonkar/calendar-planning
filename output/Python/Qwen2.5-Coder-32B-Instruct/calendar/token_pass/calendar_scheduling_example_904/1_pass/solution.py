from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Busy times for Daniel and Bradley
daniel_busy = {
    'Monday': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
                (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    'Thursday': [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
    'Friday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

bradley_busy = {
    'Monday': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                  (datetime.strptime("11:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Thursday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    'Friday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

def get_free_slots(busy_times):
    current_time = work_start
    free_slots = []
    for start, end in busy_times:
        if current_time < start:
            free_slots.append((current_time, start))
        current_time = max(current_time, end)
    if current_time < work_end:
        free_slots.append((current_time, work_end))
    return free_slots

def find_common_slot(daniel_free, bradley_free):
    for d_start, d_end in daniel_free:
        for b_start, b_end in bradley_free:
            overlap_start = max(d_start, b_start)
            overlap_end = min(d_end, b_end)
            if (overlap_end - overlap_start) >= timedelta(minutes=30):
                return overlap_start, overlap_end
    return None

# Iterate over each day to find a common slot
for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
    if (day == 'Wednesday' or day == 'Thursday') and 'Daniel' in locals():
        continue
    if (day == 'Monday' or day == 'Friday') and 'Bradley' in locals():
        continue
    if day == 'Tuesday':
        daniel_free = [slot for slot in get_free_slots(daniel_busy[day]) if slot[0] >= datetime.strptime("12:00", "%H:%M")]
        bradley_free = [slot for slot in get_free_slots(bradley_busy[day]) if slot[0] >= datetime.strptime("12:00", "%H:%M")]
    else:
        daniel_free = get_free_slots(daniel_busy[day])
        bradley_free = get_free_slots(bradley_busy[day])

    common_slot = find_common_slot(daniel_free, bradley_free)
    if common_slot:
        start_time, end_time = common_slot
        print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")
        break