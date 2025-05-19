from datetime import datetime, timedelta

# Participants' schedules
schedules = {
    'Judy': [(datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))],
    'Olivia': [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
               (datetime.strptime("12:00", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
               (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M"))],
    'Eric': [],
    'Jacqueline': [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
                   (datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M"))],
    'Laura': [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Tyler': [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
              (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
              (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
              (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
              (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    'Lisa': [(datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
             (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
             (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
             (datetime.strptime("13:00", "%H:%M"), datetime.strptime("13:30", "%H:%M")),
             (datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")),
             (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))]
}

# Meeting parameters
meeting_duration = timedelta(minutes=30)
work_hours_start = datetime.strptime("09:00", "%H:%M")
work_hours_end = datetime.strptime("17:00", "%H:%M")

# Finding a suitable time
def is_time_free(start, end):
    for busy_slots in schedules.values():
        for busy_start, busy_end in busy_slots:
            if not (end <= busy_start or start >= busy_end):
                return False
    return True

def find_meeting_time():
    time_cursor = work_hours_start
    while time_cursor + meeting_duration <= work_hours_end:
        if is_time_free(time_cursor, time_cursor + meeting_duration):
            return time_cursor, time_cursor + meeting_duration
        time_cursor += timedelta(minutes=30)  # Increment by 30 minutes
            
meeting_start, meeting_end = find_meeting_time()
day_of_week = "Monday"

# Output the format
print(f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')}")
print(day_of_week)