from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a meeting time that works for everyone's schedule.

    Args:
        start_time (int): Start time of the day in 24-hour format.
        end_time (int): End time of the day in 24-hour format.
        duration (int): Duration of the meeting in minutes.
        schedules (dict): Dictionary of schedules where each key is a person's name
            and each value is a list of tuples representing their busy times.

    Returns:
        tuple: A tuple containing the day of the week and a tuple of two times
            representing the meeting start and end times in 24-hour format.
    """
    # Initialize the day of the week
    day_of_week = datetime.now().strftime('%A')

    # Iterate over the possible meeting times
    for hour in range(start_time, end_time):
        for minute in range(0, 60 - duration + 1, 30):  # Ensure meeting duration is a multiple of 30 minutes
            # Calculate the meeting start and end times
            meeting_start = datetime.combine(datetime.now().date(), datetime(1, 1, 1, hour, minute).time())
            meeting_end = meeting_start + timedelta(minutes=duration)

            # Check if the meeting time works for everyone
            if all(not any((meeting_start < datetime.combine(datetime.now().date(), datetime(1, 1, 1, busy_time[0], busy_time[1]).time()) < meeting_end or
                            meeting_end < datetime.combine(datetime.now().date(), datetime(1, 1, 1, busy_time[0], busy_time[1]).time()) < meeting_start)
                           for busy_time in schedules.get(person, [])
                           if meeting_start >= datetime.combine(datetime.now().date(), datetime(1, 1, 1, 9, 0).time()) and meeting_end <= datetime.combine(datetime.now().date(), datetime(1, 1, 1, 17, 0).time()))
                   for person in schedules if person in schedules and schedules[person] is not None):  # Ensure person is in the schedules dictionary and has a schedule
                # If the meeting time works for everyone, return it
                return day_of_week, (meeting_start.strftime('%H:%M'), meeting_end.strftime('%H:%M'))

    # If no meeting time works for everyone, return None
    return None


# Define the schedules
schedules = {
    'Andrea': [(9, 30), (10, 30), (13, 30), (14, 30)],
    'Ruth': [(12, 30), (13, 0), (15, 0), (15, 30)],
    'Steven': [(10, 0), (10, 30), (11, 0), (11, 30), (12, 0), (12, 30), (13, 30), (14, 0), (15, 0), (16, 0)],
    'Grace': [],
    'Kyle': [(9, 0), (9, 30), (10, 30), (12, 0), (12, 30), (13, 0), (13, 30), (15, 0), (15, 30), (16, 0), (16, 30), (17, 0)],
    'Elijah': [(9, 0), (11, 0), (11, 30), (13, 0), (13, 30), (15, 30), (16, 0), (16, 30), (17, 0)],
    'Lori': [(9, 0), (9, 30), (10, 0), (11, 30), (12, 0), (13, 30), (14, 0), (16, 0), (16, 30), (17, 0)]
}

# Define the meeting duration
duration = 30

# Define the start and end times of the day
start_time = 9
end_time = 17

# Find a meeting time that works for everyone
meeting_time = find_meeting_time(start_time, end_time, duration, schedules)

# Print the meeting time
if meeting_time:
    day_of_week, (start_time, end_time) = meeting_time
    print(f"{day_of_week}: {start_time} - {end_time}")
else:
    print("No meeting time works for everyone.")