from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration):
    start_time = datetime.strptime("09:00", "%H:%M")
    end_time = datetime.strptime("17:00", "%H:%M")
    time_slot = start_time

    while time_slot + timedelta(minutes=meeting_duration) <= end_time:
        available = True
        for person, blocks in schedules.items():
            for block in blocks:
                if time_slot >= block[0] and time_slot < block[1]:
                    available = False
                    break
                elif time_slot + timedelta(minutes=meeting_duration) > block[0] and time_slot + timedelta(minutes=meeting_duration) <= block[1]:
                    available = False
                    break
            if not available:
                break
        if available:
            return time_slot.strftime("%H:%M"), (time_slot + timedelta(minutes=meeting_duration)).strftime("%H:%M")
        time_slot += timedelta(minutes=15)

schedules = {
    "Stephanie": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
                  (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:00", "%H:%M"))],
    "Joe": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("09:30", "%H:%M")),
            (datetime.strptime("10:00", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
            (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
            (datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Diana": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
              (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
              (datetime.strptime("13:00", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
              (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
              (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Deborah": [(datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:00", "%H:%M")),
                (datetime.strptime("10:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
                (datetime.strptime("12:30", "%H:%M"), datetime.strptime("13:00", "%H:%M")),
                (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")),
                (datetime.strptime("14:30", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
                (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))]
}

meeting_duration = 30
start, end = find_meeting_time(schedules, meeting_duration)
print(f"{start}:{end} Monday")