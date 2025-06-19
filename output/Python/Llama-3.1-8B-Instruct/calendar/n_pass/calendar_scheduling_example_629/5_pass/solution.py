from datetime import datetime, timedelta

def find_meeting_time(margaret_schedule, alexis_schedule, unavailable_slots, meeting_duration, day, preferred_time):
    # Filter schedules for the given day
    margaret_schedule_day = {time: duration for time, duration in margaret_schedule.items() if time[0] == day}
    alexis_schedule_day = {time: duration for time, duration in alexis_schedule.items() if time[0] == day}

    # Sort schedules by start time
    margaret_schedule_day = sorted(margaret_schedule_day.items())
    alexis_schedule_day = sorted(alexis_schedule_day.items())

    # Initialize meeting time
    meeting_time = None

    # Iterate over possible meeting times
    for hour in range(9, 17):
        for minute in range(0, 60, meeting_duration):
            # Check if meeting time is available for both participants
            meeting_start = datetime(day, 1, 1, hour, minute)
            meeting_end = meeting_start + timedelta(minutes=meeting_duration)

            # Check if meeting time conflicts with any scheduled events or unavailable time slots
            if not any(
                (meeting_start >= datetime(event[0][0], 1, 1, int(event[0][1]), 0) and meeting_start < datetime(event[0][0], 1, 1, int(event[0][1]), 14))
                or (meeting_end > datetime(event[0][0], 1, 1, int(event[0][1]), 0) and meeting_end <= datetime(event[0][0], 1, 1, int(event[0][1]), 14))
                for event in margaret_schedule_day
            ) and not any(
                (meeting_start >= datetime(event[0][0], 1, 1, int(event[0][1]), 0) and meeting_start < datetime(event[0][0], 1, 1, int(event[0][1]), 14))
                or (meeting_end > datetime(event[0][0], 1, 1, int(event[0][1]), 0) and meeting_end <= datetime(event[0][0], 1, 1, int(event[0][1]), 14))
                for event in alexis_schedule_day
            ) and not any(
                (meeting_start >= datetime(int(slot[0]), 1, 1, int(slot[1]), 0) and meeting_start < datetime(int(slot[0]), 1, 1, int(slot[1]), int(slot[1])))
                or (meeting_end > datetime(int(slot[0]), 1, 1, int(slot[1]), 0) and meeting_end <= datetime(int(slot[0]), 1, 1, int(slot[1]), int(slot[1])))
                for slot in unavailable_slots[day - 1]
            ):
                # Check if meeting time is within preferred time range
                if (day == 1 and hour >= 14 and minute >= 30) or (day == 2 and hour >= 14 and minute >= 30):
                    meeting_time = (meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M"))
                    break
                else:
                    meeting_time = (meeting_start.strftime("%H:%M"), meeting_end.strftime("%H:%M"))
                    break

        if meeting_time:
            break

    # Determine the day of the week
    if day == 1:
        day_of_week = "Monday"
    else:
        day_of_week = "Tuesday"

    return f"{day_of_week}: {meeting_time[0]}-{meeting_time[1]}"

# Define schedules
margaret_schedule = {
    (1, 9): 30, (1, 10): 30, (1, 11): 30, (1, 13): 30, (1, 15): 120,
    (2, 12): 30
}
alexis_schedule = {
    (1, 9): 60, (1, 10): 60, (1, 12): 30, (1, 14): 180, (1, 17): 120,
    (2, 9): 30, (2, 10): 30, (2, 14): 150
}

# Define unavailable time slots
unavailable_slots = [
    [(1, 9), (1, 14.5)],  # Monday
    [(1, 9), (1, 14.5)]  # Tuesday
]

# Define meeting duration
meeting_duration = 30

# Define day and preferred time
day = 2
preferred_time = True

# Find meeting time
print(find_meeting_time(margaret_schedule, alexis_schedule, unavailable_slots, meeting_duration, day, preferred_time))