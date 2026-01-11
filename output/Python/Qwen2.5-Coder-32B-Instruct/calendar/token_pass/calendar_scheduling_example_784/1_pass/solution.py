from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Blocked times
judith_blocked_times = {
    'Monday': [(datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    'Wednesday': [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M"))]
}

timothy_blocked_times = {
    'Monday': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
               (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
               (datetime.strptime("12:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("09:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Wednesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
                  (datetime.strptime("10:30", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
                  (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
                  (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                  (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

def find_free_slots(day):
    judith_blocks = judith_blocked_times.get(day, [])
    timothy_blocks = timothy_blocked_times.get(day, [])
    all_blocks = sorted(judith_blocks + timothy_blocks)
    
    current_start = work_start
    free_slots = []
    
    for start_block, end_block in all_blocks:
        if current_start < start_block:
            free_slots.append((current_start, start_block))
        current_start = max(current_start, end_block)
    
    if current_start < work_end:
        free_slots.append((current_start, work_end))
    
    return free_slots

def find_meeting_time():
    days_to_check = ['Monday', 'Tuesday', 'Wednesday']
    for day in days_to_check:
        free_slots = find_free_slots(day)
        for start, end in free_slots:
            if (day != 'Monday' or start.hour >= 12) and (day != 'Wednesday' or start.hour >= 12):
                if end - start >= timedelta(hours=1):
                    return f"{start.strftime('%H:%M')}:{(start + timedelta(hours=1)).strftime('%H:%M')}", day
    return None, None

meeting_time, meeting_day = find_meeting_time()
print(f"Meeting time: {meeting_time} on {meeting_day}")