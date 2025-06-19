from datetime import datetime, timedelta
import calendar

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

    # Iterate over each possible day of the week
    for day in range(0, 7):
        # Get the date of the start time
        start_date = start_time.date()

        # Get the date of the current day
        current_date = start_date + timedelta(days=day)

        # Get the start and end times of the current day
        current_start_time = datetime(current_date.year, current_date.month, current_date.day, start_time.hour, start_time.minute)
        current_end_time = datetime(current_date.year, current_date.month, current_date.day, end_time.hour, end_time.minute)

        # Check if the current day is a weekday
        if calendar.weekday(current_date.year, current_date.month, current_date.day) < 5:
            # Find the optimal meeting time for the current day
            optimal_time = find_optimal_time(current_start_time, current_end_time, meeting_duration, schedules)

            # If an optimal meeting time is found, return it
            if optimal_time:
                meeting_time_found = True
                return (f"{optimal_time[0].strftime('%H:%M')}:{(optimal_time[0] + meeting_duration).strftime('%H:%M')}", optimal_time[0].strftime('%A'))

    # If no meeting time is found, return a message
    return "No meeting time found within the given constraints."

def find_optimal_time(start_time, end_time, meeting_duration, schedules):
    """
    Find the optimal meeting time for the given day.

    Args:
    start_time (datetime): Start of the work hours.
    end_time (datetime): End of the work hours.
    meeting_duration (timedelta): Duration of the meeting.
    schedules (dict): Existing schedules for each participant.

    Returns:
    tuple: Optimal meeting time and day of the week.
    """
    # Initialize the optimal time to None
    optimal_time = None

    # Iterate over each possible meeting time
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60):
            # Create a datetime object for the current time
            current_time = start_time.replace(hour=hour, minute=minute)

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

                # If no conflicts are found, update the optimal time
                if not conflicts and (not optimal_time or current_time < optimal_time[0]):
                    optimal_time = (current_time, end_time)

    # Return the optimal time
    return optimal_time

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