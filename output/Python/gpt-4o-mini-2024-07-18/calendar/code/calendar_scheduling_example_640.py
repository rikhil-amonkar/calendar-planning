from datetime import datetime, timedelta

# Define work hours and constraints for Bobby and Michael
work_hours = {
    'Monday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Tuesday': [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

bobby_busy = {
    'Monday': [(datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    'Tuesday': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
        (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
}

michael_busy = {
    'Monday': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
        (datetime.strptime("10:30", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
        (datetime.strptime("14:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
        (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ],
    'Tuesday': [
        (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
        (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
        (datetime.strptime("12:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
        (datetime.strptime("15:00", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
        (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")),
    ]
}

meeting_duration = timedelta(minutes=30)

# Function to find the first available time slot
def find_meeting_time():
    for day, hours in work_hours.items():
        for work_start, work_end in hours:
            available_start = work_start
            while available_start + meeting_duration <= work_end:
                is_conflict = False
                for b_start, b_end in bobby_busy.get(day, []):
                    if not (available_start + meeting_duration <= b_start or available_start >= b_end):
                        is_conflict = True
                        break
                for m_start, m_end in michael_busy.get(day, []):
                    if not (available_start + meeting_duration <= m_start or available_start >= m_end):
                        is_conflict = True
                        break
                if not is_conflict:
                    return (available_start, available_start + meeting_duration, day)
                available_start += timedelta(minutes=1)
    return None

meeting_time = find_meeting_time()
if meeting_time:
    start_time, end_time, day = meeting_time
    print(f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}")