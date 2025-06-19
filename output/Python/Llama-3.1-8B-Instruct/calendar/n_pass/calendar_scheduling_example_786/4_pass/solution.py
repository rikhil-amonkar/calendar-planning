from datetime import datetime, timedelta

def find_meeting_time(amy_schedule, pamela_schedule, meeting_duration, preferences):
    """
    Find a suitable time for a meeting between Amy and Pamela.

    Args:
    amy_schedule (dict): Amy's schedule with busy times as tuples of (start, end).
    pamela_schedule (dict): Pamela's schedule with busy times as tuples of (start, end).
    meeting_duration (int): The duration of the meeting in minutes.
    preferences (dict): Preferences for meeting time, e.g., 'avoid_monday', 'avoid_tuesday', 'avoid_before_16:00'.

    Returns:
    tuple: A proposed meeting time as (day, start_time, end_time) and a boolean indicating whether the time is valid.
    """

    # Define the work hours and days
    work_hours = (9, 17)
    work_days = ['Monday', 'Tuesday', 'Wednesday']

    # Initialize the proposed meeting time
    proposed_time = None

    # Iterate over each day
    for day in work_days:
        # Iterate over each hour in the work hours
        for hour in range(work_hours[0], work_hours[1]):
            # Convert the hour to a datetime object
            start_time = datetime.strptime(f'{day} {hour}:00', '%A %H:%M')
            end_time = start_time + timedelta(minutes=meeting_duration)

            # Check if the time is within the work hours
            if start_time.hour >= work_hours[0] and end_time.hour <= work_hours[1]:
                # Convert the busy times to datetime objects
                amy_busy_times = []
                for amy_start, amy_end in amy_schedule.get(day, []):
                    amy_start_time = datetime.strptime(f'{day} {amy_start}', '%A %H')
                    amy_end_time = datetime.strptime(f'{day} {amy_end}', '%A %H')
                    amy_busy_times.append((amy_start_time, amy_end_time))

                pamela_busy_times = []
                for pamela_start, pamela_end in pamela_schedule.get(day, []):
                    pamela_start_time = datetime.strptime(f'{day} {pamela_start}', '%A %H')
                    pamela_end_time = datetime.strptime(f'{day} {pamela_end}', '%A %M')  # Changed to %A %M
                    pamela_busy_times.append((pamela_start_time, pamela_end_time))

                # Check if the time is not busy for Amy
                if not any(start_time >= amy_start_time and end_time <= amy_end_time for amy_start_time, amy_end_time in amy_busy_times):
                    # Check if the time is not busy for Pamela
                    if not any(start_time >= pamela_start_time and end_time <= pamela_end_time for pamela_start_time, pamela_end_time in pamela_busy_times):
                        # Check if the time meets the preferences
                        if not (preferences.get('avoid_monday') and day == 'Monday') and \
                           not (preferences.get('avoid_tuesday') and day == 'Tuesday') and \
                           not (preferences.get('avoid_before_16:00') and start_time.hour < 16):
                            # If all conditions are met, propose this time
                            proposed_time = (day, start_time.strftime('%H:%M'), end_time.strftime('%H:%M'))
                            break

        # If a proposed time is found, break the loop
        if proposed_time:
            break

    return proposed_time


# Define the schedules and preferences
amy_schedule = {
    'Monday': [],
    'Tuesday': [],
    'Wednesday': [('Monday', '11'), ('Monday', '11.5'), ('Monday', '13.5'), ('Monday', '14')]
}

pamela_schedule = {
    'Monday': [('Monday', '9'), ('Monday', '10.5'), ('Monday', '11'), ('Monday', '16.5')],
    'Tuesday': [('Tuesday', '9'), ('Tuesday', '9.5'), ('Tuesday', '10'), ('Tuesday', '17')],
    'Wednesday': [('Wednesday', '9'), ('Wednesday', '9.5'), ('Wednesday', '10'), ('Wednesday', '11'), ('Wednesday', '11.5'), ('Wednesday', '13.5'), ('Wednesday', '14.5'), ('Wednesday', '15'), ('Wednesday', '16'), ('Wednesday', '16.5')]
}

preferences = {
    'avoid_monday': False,
    'avoid_tuesday': False,
    'avoid_before_16:00': False
}

meeting_duration = 30  # minutes

# Find and print the proposed meeting time
proposed_time = find_meeting_time(amy_schedule, pamela_schedule, meeting_duration, preferences)
if proposed_time:
    print(f'{proposed_time[1]} - {proposed_time[2]} on {proposed_time[0]}')
else:
    print('No proposed time found.')