from datetime import datetime, timedelta

# Define work hours
work_start = datetime.strptime("09:00", "%H:%M")
work_end = datetime.strptime("17:00", "%H:%M")

# Blocked times for each participant
martha_blocked = {
    "Monday": [datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")],
    "Tuesday": [datetime.strptime("15:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")],
    "Wednesday": [datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M"),
                  datetime.strptime("14:00", "%H:%M"), datetime.strptime("14:30", "%H:%M")]
}

beverly_blocked = {
    "Monday": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("13:30", "%H:%M"),
               datetime.strptime("14:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")],
    "Tuesday": [datetime.strptime("09:00", "%H:%M"), datetime.strptime("17:00", "%H:%M")],
    "Wednesday": [datetime.strptime("09:30", "%H:%M"), datetime.strptime("15:30", "%H:%M"),
                  datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M")]
}

def is_time_free(day, time, blocked_times):
    for start, end in zip(blocked_times[day][::2], blocked_times[day][1::2]):
        if start <= time < end:
            return False
    return True

def find_meeting_time():
    for day in ["Monday", "Tuesday", "Wednesday"]:
        current_time = work_start
        while current_time + timedelta(hours=1) <= work_end:
            if is_time_free(day, current_time, martha_blocked) and is_time_free(day, current_time, beverly_blocked):
                return f"{day} {current_time.strftime('%H:%M')}:{(current_time + timedelta(hours=1)).strftime('%H:%M')}"
            current_time += timedelta(minutes=30)  # Increment by half an hour to check all possible slots

meeting_time = find_meeting_time()
print(meeting_time)