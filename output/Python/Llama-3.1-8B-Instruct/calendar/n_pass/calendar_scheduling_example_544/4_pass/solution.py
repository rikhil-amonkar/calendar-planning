from datetime import datetime, timedelta

def find_meeting_time(deborah_schedule, albert_schedules, meeting_duration, max_meeting_time):
    # Generate all possible meeting times
    possible_meeting_times = []
    for hour in range(9, 17):
        for minute in range(0, 60, meeting_duration):
            time = datetime(2024, 1, 1, hour, minute)
            end_time = time + timedelta(minutes=meeting_duration)
            possible_meeting_times.append((time, end_time))

    # Filter out times that don't work for Deborah
    deborah_works = []
    for time, end_time in possible_meeting_times:
        if time >= deborah_schedule[0] and end_time <= deborah_schedule[1]:
            deborah_works.append((time, end_time))

    # Filter out times that don't work for Albert
    albert_works = []
    for time, end_time in deborah_works:
        works_for_albert = True
        for albert_schedule in albert_schedules:
            # Get the schedule and unavailable times from the dictionary
            schedule = albert_schedule["schedule"]
            unavailable_times = albert_schedule["unavailable_times"]
            if schedule[0] < end_time and schedule[1] > time:
                # Check if the meeting time conflicts with an unavailable time slot
                for unavailable_time in unavailable_times:
                    if unavailable_time[0] < end_time and unavailable_time[1] > time:
                        works_for_albert = False
                        break
                if not works_for_albert:
                    break
        if works_for_albert:
            albert_works.append((time, end_time))

    # Filter out times that are too late for Albert
    albert_works = [time for time in albert_works if time[0] <= max_meeting_time]

    # Find the first time that works for both Deborah and Albert
    meeting_time = None
    for time, end_time in albert_works:
        if time >= deborah_schedule[0] and end_time <= deborah_schedule[1]:
            meeting_time = (time.strftime("%H:%M"), end_time.strftime("%H:%M"))
            break

    # Return the day of the week and the meeting time
    if meeting_time:
        return f"{time.strftime('%A')} {meeting_time[0]} - {meeting_time[1]}"
    else:
        return "No meeting time found"

# Define the schedules for Deborah and Albert
deborah_schedule = (datetime(2024, 1, 1, 9, 0), datetime(2024, 1, 1, 17, 0))
albert_schedules = [
    {
        "schedule": (datetime(2024, 1, 1, 9, 0), datetime(2024, 1, 1, 10, 0)),
        "unavailable_times": [
            (datetime(2024, 1, 1, 9, 30), datetime(2024, 1, 1, 10, 0))
        ]
    },
    {
        "schedule": (datetime(2024, 1, 1, 10, 30), datetime(2024, 1, 1, 12, 0)),
        "unavailable_times": []
    },
    {
        "schedule": (datetime(2024, 1, 1, 15, 0), datetime(2024, 1, 1, 16, 30)),
        "unavailable_times": []
    }
]
max_meeting_time = datetime(2024, 1, 1, 11, 0)

# Define the meeting duration
meeting_duration = 30  # minutes

# Find and print the meeting time
print(find_meeting_time(deborah_schedule, albert_schedules, meeting_duration, max_meeting_time))