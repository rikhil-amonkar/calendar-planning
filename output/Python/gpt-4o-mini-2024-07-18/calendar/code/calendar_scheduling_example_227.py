from datetime import datetime, timedelta

# Scheduling constraints
meeting_duration = timedelta(minutes=30)
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Participants' availability
david_busy = [(datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
               (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]

douglas_busy = [(datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))]

ralph_busy = [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")),
               (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")),
               (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
               (datetime.strptime("13:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
               (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
               (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

jordan_busy = [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                 (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
                 (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
                 (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
                 (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]

participants_busy = [david_busy, douglas_busy, ralph_busy, jordan_busy]

def is_time_available(start_time, duration):
    end_time = start_time + duration
    for busy_slots in participants_busy:
        for busy_start, busy_end in busy_slots:
            if (start_time < busy_end and end_time > busy_start):
                return False
    return True

# Searching for a suitable time slot starting from 14:00
proposed_start = datetime.strptime("14:00", "%H:%M")

while proposed_start + meeting_duration <= work_end:
    if is_time_available(proposed_start, meeting_duration):
        proposed_end = proposed_start + meeting_duration
        print(f"{proposed_start.strftime('%H:%M')}:{proposed_end.strftime('%H:%M')}\nMonday")
        break
    proposed_start += timedelta(minutes=1)