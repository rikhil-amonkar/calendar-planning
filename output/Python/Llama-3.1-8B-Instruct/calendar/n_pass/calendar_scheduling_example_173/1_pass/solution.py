from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (datetime): Start of the work hours.
    end_time (datetime): End of the work hours.
    duration (int): Duration of the meeting in minutes.
    schedules (dict): Existing schedules for each participant.

    Returns:
    tuple: Proposed time range and day of the week.
    """
    # Convert duration to timedelta
    meeting_duration = timedelta(minutes=duration)

    # Initialize a flag to check if a meeting time is found
    meeting_time_found = False

    # Iterate over each possible meeting time
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60):
            # Create a datetime object for the current time
            current_time = start_time.replace(hour=hour, minute=minute)

            # Check if the current time is within the work hours
            if start_time <= current_time < end_time:
                # Check if the current time plus the meeting duration is within the work hours
                if current_time + meeting_duration <= end_time:
                    # Check if the current time and the current time plus the meeting duration do not conflict with any schedules
                    conflicts = False
                    for name, schedule in schedules.items():
                        for time in schedule:
                            if (current_time >= time[0] and current_time < time[1]) or \
                               (current_time + meeting_duration >= time[0] and current_time + meeting_duration < time[1]):
                                conflicts = True
                                break
                        if conflicts:
                            break
                    # If no conflicts are found, return the meeting time and day of the week
                    if not conflicts:
                        meeting_time_found = True
                        return (f"{current_time.strftime('%H:%M')}:{(current_time + meeting_duration).strftime('%H:%M')}", current_time.strftime('%A'))

    # If no meeting time is found, return a message
    return "No meeting time found within the given constraints."

# Define the existing schedules for each participant
schedules = {
    "Jacqueline": [(datetime(2024, 7, 29, 9), datetime(2024, 7, 29, 9, 30)),
                   (datetime(2024, 7, 29, 11), datetime(2024, 7, 29, 11, 30)),
                   (datetime(2024, 7, 29, 12, 30), datetime(2024, 7, 29, 13)),
                   (datetime(2024, 7, 29, 15, 30), datetime(2024, 7, 29, 16))],
    "Harold": [(datetime(2024, 7, 29, 10), datetime(2024, 7, 29, 10, 30)),
               (datetime(2024, 7, 29, 13), datetime(2024, 7, 29, 13, 30)),
               (datetime(2024, 7, 29, 15), datetime(2024, 7, 29, 17))],
    "Arthur": [(datetime(2024, 7, 29, 9), datetime(2024, 7, 29, 9, 30)),
               (datetime(2024, 7, 29, 10), datetime(2024, 7, 29, 12, 30)),
               (datetime(2024, 7, 29, 14, 30), datetime(2024, 7, 29, 15)),
               (datetime(2024, 7, 29, 15, 30), datetime(2024, 7, 29, 17))],
    "Kelly": [(datetime(2024, 7, 29, 9), datetime(2024, 7, 29, 9, 30)),
              (datetime(2024, 7, 29, 10), datetime(2024, 7, 29, 11)),
              (datetime(2024, 7, 29, 11, 30), datetime(2024, 7, 29, 12, 30)),
              (datetime(2024, 7, 29, 14), datetime(2024, 7, 29, 15)),
              (datetime(2024, 7, 29, 15, 30), datetime(2024, 7, 29, 16))]
}

# Define the start and end of the work hours
start_time = datetime(2024, 7, 29, 9)
end_time = datetime(2024, 7, 29, 17)

# Define the meeting duration
duration = 30

# Find a meeting time that works for everyone's schedule and constraints
meeting_time = find_meeting_time(start_time, end_time, duration, schedules)

# Print the meeting time and day of the week
print(f"Proposed meeting time: {meeting_time[0]} on {meeting_time[1]}")