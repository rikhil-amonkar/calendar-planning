from datetime import datetime, timedelta

def find_meeting_time(daniel_schedule, bradley_schedule, meeting_duration, preferences):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    preferred_days = set(preferences["daniel"]) & set(preferences["bradley"])
    other_days = [day for day in days if day not in preferred_days]

    for day in preferred_days:
        daniel_available = []
        bradley_available = []
        start_time = 9 * 60
        end_time = 17 * 60

        # Adjust Bradley's schedule for "before 12:00" preference
        if "before 12:00" in preferences["bradley"] and day in preferences["bradley"]:
            bradley_schedule[day] = [(time[0], time[1]) for time in bradley_schedule[day] if time[1] <= 12 * 60]

        for time in daniel_schedule[day]:
            start, end = time
            daniel_available.extend([(start + i, end + i) for i in range(start, end, 30)])

        for time in bradley_schedule[day]:
            start, end = time
            bradley_available.extend([(start + i, end + i) for i in range(start, end, 30)])

        available_times = []
        for time in daniel_available:
            if time in bradley_available and time[0] + meeting_duration <= end_time:
                available_times.append(time)

        if available_times:
            start_time = min(available_times, key=lambda x: x[0])[0]
            end_time = start_time + meeting_duration
            if end_time <= end_time:
                return f"{day}, {datetime.fromtimestamp(start_time / 60).strftime('%H:%M')} - {datetime.fromtimestamp(end_time / 60).strftime('%H:%M')}"

    for day in other_days:
        daniel_available = []
        bradley_available = []
        start_time = 9 * 60
        end_time = 17 * 60

        for time in daniel_schedule[day]:
            start, end = time
            daniel_available.extend([(start + i, end + i) for i in range(start, end, 30)])

        for time in bradley_schedule[day]:
            start, end = time
            bradley_available.extend([(start + i, end + i) for i in range(start, end, 30)])

        available_times = []
        for time in daniel_available:
            if time in bradley_available and time[0] + meeting_duration <= end_time:
                available_times.append(time)

        if available_times:
            start_time = min(available_times, key=lambda x: x[0])[0]
            end_time = start_time + meeting_duration
            if end_time <= end_time:
                return f"{day}, {datetime.fromtimestamp(start_time / 60).strftime('%H:%M')} - {datetime.fromtimestamp(end_time / 60).strftime('%H:%M')}"

    return "No available time found"

# Existing schedules
daniel_schedule = {
    "Monday": [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (12 * 60, 12 * 60 + 30), (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    "Tuesday": [(11 * 60, 12 * 60), (13 * 60, 13 * 60 + 30), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
    "Wednesday": [(9 * 60, 10 * 60), (14 * 60, 14 * 60 + 30)],
    "Thursday": [(10 * 60 + 30, 11 * 60), (12 * 60, 13 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60)],
    "Friday": [(9 * 60, 9 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60, 13 * 60 + 30), (16 * 60 + 30, 17 * 60)]
}

bradley_schedule = {
    "Monday": [(9 * 60 + 30, 11 * 60), (11 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 15 * 60)],
    "Tuesday": [(10 * 60 + 30, 11 * 60), (12 * 60, 13 * 60), (13 * 60 + 30, 14 * 60), (15 * 60 + 30, 16 * 60 + 30)],
    "Wednesday": [(9 * 60, 10 * 60), (11 * 60, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 17 * 60)],
    "Thursday": [(9 * 60, 12 * 60 + 30), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60 + 30)],
    "Friday": [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), (15 * 60 + 30, 16 * 60 + 30)]
}

preferences = {
    "daniel": ["Wednesday", "Thursday"],
    "bradley": ["Monday", "Tuesday before 12:00", "Friday"]
}

meeting_duration = 30 * 60

print(find_meeting_time(daniel_schedule, bradley_schedule, meeting_duration, preferences))