from datetime import datetime, timedelta

def find_meeting_time(evelyn_schedule, randy_schedule, evelyn_preference_end, meeting_duration):
    work_start = datetime.strptime("09:00", "%H:%M")
    work_end = datetime.strptime("17:00", "%H:%M")
    evelyn_preference_end = datetime.strptime(evelyn_preference_end, "%H:%M")
    meeting_duration = timedelta(minutes=meeting_duration)

    available_slots = []

    # Combine all busy times into one list and sort it
    all_busy_times = sorted(evelyn_schedule + randy_schedule, key=lambda x: x[0])

    current_time = work_start

    for start, end in all_busy_times:
        if current_time < start:
            available_slots.append((current_time, start))
        current_time = max(current_time, end)

    if current_time < work_end:
        available_slots.append((current_time, work_end))

    # Find a slot that fits the meeting duration and Evelyn's preference
    for start, end in available_slots:
        if end - start >= meeting_duration and start < evelyn_preference_end:
            meeting_start = start
            meeting_end = start + meeting_duration
            return meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M")

    return None

# Define the schedules
evelyn_schedule = []
randy_schedule = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")),
    (datetime.strptime("11:00", "%H:%M"), datetime.strptime("15:30", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

# Define preferences and meeting duration
evelyn_preference_end = "13:00"
meeting_duration = 30  # in minutes

# Find the meeting time
meeting_start, meeting_end = find_meeting_time(evelyn_schedule, randy_schedule, evelyn_preference_end, meeting_duration)

print(f"{meeting_start}:{meeting_end} Monday")