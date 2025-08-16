from datetime import datetime, timedelta

def find_meeting_time(gary_schedule, david_schedule, meeting_duration, work_start, work_end, days):
    meeting_duration = timedelta(hours=meeting_duration)
    work_start = datetime.strptime(work_start, "%H:%M")
    work_end = datetime.strptime(work_end, "%H:%M")

    for day in days:
        gary_blocked = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), slot.split(" to "))) for slot in gary_schedule[day]]
        david_blocked = [tuple(map(lambda x: datetime.strptime(x, "%H:%M"), slot.split(" to "))) for slot in david_schedule[day]]

        current_time = work_start
        while current_time + meeting_duration <= work_end:
            available = True
            for block in gary_blocked + david_blocked:
                if not (current_time + meeting_duration <= block[0] or current_time >= block[1]):
                    available = False
                    break
            if available:
                return f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", day
            current_time += timedelta(minutes=30)  # Check every half-hour

gary_schedule = {
    "Monday": ["9:30 to 10:00", "11:00 to 13:00", "14:00 to 14:30", "16:30 to 17:00"],
    "Tuesday": ["9:00 to 9:30", "10:30 to 11:00", "14:30 to 16:00"]
}

david_schedule = {
    "Monday": ["9:00 to 9:30", "10:00 to 13:00", "14:30 to 16:30"],
    "Tuesday": ["9:00 to 9:30", "10:00 to 10:30", "11:00 to 12:30", "13:00 to 14:30", "15:00 to 16:00", "16:30 to 17:00"]
}

meeting_time, meeting_day = find_meeting_time(gary_schedule, david_schedule, 1, "09:00", "17:00", ["Monday", "Tuesday"])
print(f"{meeting_time}, {meeting_day}")