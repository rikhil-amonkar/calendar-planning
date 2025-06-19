from datetime import datetime, timedelta

def find_meeting_time(jean_schedule, doris_schedule, meeting_duration, day):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        jean_schedule (list): Jean's schedule for the day.
        doris_schedule (list): Doris's schedule for the day.
        meeting_duration (int): The duration of the meeting in minutes.
        day (str): The day of the week.

    Returns:
        tuple: A proposed time and day that works for everyone's schedule and constraints.
    """

    # Sort the schedules by start time
    jean_schedule.sort(key=lambda x: x[0])
    doris_schedule.sort(key=lambda x: x[0])

    # Initialize the current time to 9:00
    current_time = datetime.strptime(f"{day} 09:00", "%A %H:%M")

    # Loop through the schedules to find a time that works for everyone
    while current_time < datetime.strptime(f"{day} 17:00", "%A %H:%M"):
        # Check if the current time works for Jean
        jean_time_slots = [(start, end) for start, end in jean_schedule if current_time >= start and current_time + timedelta(minutes=meeting_duration) <= end]
        if len(jean_time_slots) == 0:
            # If Jean has no time slots, check if the current time fits within any of Jean's time slots
            jean_time_slots = [(start, end) for start, end in jean_schedule if (start < current_time < end) or (start < current_time + timedelta(minutes=meeting_duration) < end)]
        if len(jean_time_slots) == 0:
            # If the current time does not fit within any of Jean's time slots, move to the next time slot
            current_time += timedelta(minutes=30)
            continue

        # Check if the current time works for Doris
        doris_time_slots = [(start, end) for start, end in doris_schedule if current_time >= start and current_time + timedelta(minutes=meeting_duration) <= end]
        if len(doris_time_slots) == 0:
            # If Doris has no time slots, check if the current time fits within any of Doris's time slots
            doris_time_slots = [(start, end) for start, end in doris_schedule if (start < current_time < end) or (start < current_time + timedelta(minutes=meeting_duration) < end)]
        if len(doris_time_slots) == 0:
            # If the current time does not fit within any of Doris's time slots, move to the next time slot
            current_time += timedelta(minutes=30)
            continue

        # Check if Doris would rather not meet on Monday after 14:00
        if day == "Monday" and current_time.hour >= 14:
            # If Doris would rather not meet, try the next day
            if day == "Monday":
                day = "Tuesday"
                current_time = datetime.strptime(f"{day} 09:00", "%A %H:%M")
            else:
                # If the current time works, return it
                return f"{current_time.strftime('%H:%M')} - {current_time + timedelta(minutes=meeting_duration).strftime('%H:%M')}", day
        else:
            # If the current time works, return it
            return f"{current_time.strftime('%H:%M')} - {current_time + timedelta(minutes=meeting_duration).strftime('%H:%M')}", day

        # Move to the next time slot
        current_time += timedelta(minutes=30)

    # If no time is found, return None
    return None


# Define the schedules
jean_schedule = [
    (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")),
    (datetime.strptime("16:00", "%H:%M"), datetime.strptime("16:30", "%H:%M"))
]

doris_schedule = [
    (datetime.strptime("09:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")),
    (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")),
    (datetime.strptime("13:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")),
    (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))
]

# Find a meeting time
meeting_duration = 30  # 30 minutes
day = "Monday"
result = find_meeting_time(jean_schedule, doris_schedule, meeting_duration, day)

# Print the result
if result:
    print(f"Proposed meeting time: {result[0]} on {result[1]}")
else:
    print("No meeting time found.")