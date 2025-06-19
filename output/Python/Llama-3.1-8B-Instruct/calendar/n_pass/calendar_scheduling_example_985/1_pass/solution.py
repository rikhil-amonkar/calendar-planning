from datetime import datetime, timedelta

def find_meeting_time(diane_schedule, matthew_schedule, meeting_duration, preferences=None):
    """
    Find a suitable time for a meeting between Diane and Matthew.

    Args:
        diane_schedule (dict): Diane's schedule with day as key and list of busy times as value.
        matthew_schedule (dict): Matthew's schedule with day as key and list of busy times as value.
        meeting_duration (int): Meeting duration in minutes.
        preferences (dict, optional): Preferences for meeting time. Defaults to None.

    Returns:
        tuple: Proposed meeting time and day of the week.
    """
    # Define days of the week
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Iterate over each day
    for day in days:
        # Get Diane's busy times for the day
        diane_busy = diane_schedule.get(day, [])

        # Get Matthew's busy times for the day
        matthew_busy = matthew_schedule.get(day, [])

        # Iterate over each hour
        for hour in range(9, 17):
            # Iterate over each minute
            for minute in range(0, 60, meeting_duration):
                # Check if the time slot is available for both Diane and Matthew
                if not any(start <= hour < end or start < hour < end + meeting_duration for start, end in diane_busy) and \
                   not any(start <= hour < end or start < hour < end + meeting_duration for start, end in matthew_busy):
                    # Check if the time slot is preferred
                    if preferences and day == preferences.get('day') and hour == preferences.get('hour'):
                        return f"{hour}:{minute:02d}-{(hour + 1) % 24}:{(minute + meeting_duration) % 60:02d}", day

                    # Return the first available time slot
                    return f"{hour}:{minute:02d}-{(hour + 1) % 24}:{(minute + meeting_duration) % 60:02d}", day

    # If no time slot is available, return None
    return None


# Define Diane's and Matthew's schedules
diane_schedule = {
    'Monday': [(9, 12), (12, 12.5), (15, 15.5)],
    'Tuesday': [(10, 11), (11.5, 12), (12.5, 13), (16, 17)],
    'Wednesday': [(9, 9.5), (14.5, 15), (16.5, 17)],
    'Thursday': [(15.5, 16.5)],
    'Friday': [(9.5, 11.5), (14.5, 15), (16, 17)]
}

matthew_schedule = {
    'Monday': [(9, 10), (10.5, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 11), (12, 14.5), (16, 17)],
    'Thursday': [(9, 16)],
    'Friday': [(9, 17)]
}

# Define preferences
preferences = {
    'day': 'Friday',
    'hour': 14
}

# Find a suitable time for the meeting
meeting_time = find_meeting_time(diane_schedule, matthew_schedule, 60, preferences)

# Print the result
if meeting_time:
    print(f"Proposed meeting time: {meeting_time[0]} on {meeting_time[1]}")
else:
    print("No suitable time found")