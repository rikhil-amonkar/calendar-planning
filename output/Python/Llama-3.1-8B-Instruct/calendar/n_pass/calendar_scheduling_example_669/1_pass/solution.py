from datetime import datetime, timedelta

def find_meeting_time(jean_schedule, doris_schedule, meeting_duration, day):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        jean_schedule (dict): Jean's schedule for the day.
        doris_schedule (dict): Doris's schedule for the day.
        meeting_duration (int): The duration of the meeting in minutes.
        day (str): The day of the week.

    Returns:
        tuple: A proposed time and day that works for everyone's schedule and constraints.
    """

    # Sort the schedules by start time
    jean_schedule = sorted(jean_schedule.items())
    doris_schedule = sorted(doris_schedule.items())

    # Initialize the current time to 9:00
    current_time = datetime.strptime(f"{day} 09:00", "%A %H:%M")

    # Loop through the schedules to find a time that works for everyone
    while current_time < datetime.strptime(f"{day} 17:00", "%A %H:%M"):
        # Check if the current time works for Jean
        if (current_time, current_time + timedelta(minutes=meeting_duration)) not in jean_schedule:
            # Check if the current time works for Doris
            if (current_time, current_time + timedelta(minutes=meeting_duration)) not in doris_schedule:
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
jean_schedule = {
    "Monday": [(1130, 1200), (1600, 1630)],
    "Tuesday": [(1130, 1200), (1600, 1630)]
}

doris_schedule = {
    "Monday": [(900, 1130), (1200, 1230), (1330, 1600), (1630, 1700)],
    "Tuesday": [(900, 1700)]
}

# Find a meeting time
meeting_duration = 30  # 30 minutes
day = "Monday"
result = find_meeting_time(jean_schedule["Monday"], doris_schedule["Monday"], meeting_duration, day)

# Print the result
if result:
    print(f"Proposed meeting time: {result[0]} on {result[1]}")
else:
    print("No meeting time found.")