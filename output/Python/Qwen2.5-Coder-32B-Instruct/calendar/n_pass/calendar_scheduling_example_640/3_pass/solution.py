from datetime import datetime, timedelta, time

def find_meeting_time(bobby_schedule, michael_schedule, meeting_duration, start_time, end_time, days):
    meeting_duration = timedelta(hours=meeting_duration)
    start_time = time.fromisoformat(start_time)
    end_time = time.fromisoformat(end_time)

    for day in days:
        bobby_busy = [tuple(map(lambda x: time.fromisoformat(x), slot.split(" to "))) for slot in bobby_schedule.get(day, [])]
        michael_busy = [tuple(map(lambda x: time.fromisoformat(x), slot.split(" to "))) for slot in michael_schedule.get(day, [])]

        current_time = start_time
        while current_time <= end_time - meeting_duration:
            available = True
            for busy_period in bobby_busy + michael_busy:
                if current_time < busy_period[1] and current_time + meeting_duration > busy_period[0]:
                    available = False
                    current_time = max(current_time, busy_period[1])
                    break
            if available:
                return current_time.isoformat(timespec='minutes'), (current_time + meeting_duration).isoformat(timespec='minutes'), day
            current_time += timedelta(minutes=30)

    return None, None, None

bobby_schedule = {
    "Monday": ["14:30 to 15:00"],
    "Tuesday": ["9:00 to 11:30", "12:00 to 12:30", "13:00 to 15:00", "15:30 to 17:00"]
}

michael_schedule = {
    "Monday": ["9:00 to 10:00", "10:30 to 13:30", "14:00 to 15:00", "15:30 to 17:00"],
    "Tuesday": ["9:00 to 10:30", "11:00 to 11:30", "12:00 to 14:00", "15:00 to 16:00", "16:30 to 17:00"]
}

meeting_duration = 0.5
start_time = "9:00"
end_time = "17:00"
days = ["Monday", "Tuesday"]

start, end, day = find_meeting_time(bobby_schedule, michael_schedule, meeting_duration, start_time, end_time, days)
if start and end and day:
    print(f"Meeting time: {start} to {end}, Day: {day}")
else:
    print("No available meeting time found.")