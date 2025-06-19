from datetime import datetime, timedelta

def find_meeting_time(nicole_schedule, ruth_schedule, meeting_duration, preferences):
    """
    Find a suitable time for a meeting between Nicole and Ruth.

    Args:
    nicole_schedule (dict): Nicole's schedule for Monday, Tuesday, and Wednesday.
    ruth_schedule (dict): Ruth's schedule for Monday, Tuesday, and Wednesday.
    meeting_duration (int): The duration of the meeting in minutes.
    preferences (list): A list of preferred days for the meeting.

    Returns:
    tuple: A tuple containing the day of the week and the meeting time in the format HH:MM-HH:MM.
    """

    # Define the start and end of the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Convert the schedules to datetime objects
    nicole_schedule = {day: [datetime.strptime(time, '%H:%M') for time in schedule] for day, schedule in nicole_schedule.items()}
    ruth_schedule = {day: [datetime.strptime(time, '%H:%M') for time in schedule] for day, schedule in ruth_schedule.items()}

    # Filter the schedules to only include the preferred days
    for day in list(nicole_schedule.keys()):
        if day not in preferences:
            del nicole_schedule[day]
    for day in list(ruth_schedule.keys()):
        if day not in preferences:
            del ruth_schedule[day]

    # Iterate over the days and find a suitable time for the meeting
    for day in nicole_schedule:
        for start in nicole_schedule[day]:
            if start.hour < 9 or start.hour >= 17:
                continue
            for end in nicole_schedule[day]:
                if end.hour < 9 or end.hour >= 17:
                    continue
                if start < end:
                    # Check if the meeting time is available for Ruth
                    for ruth_start in ruth_schedule[day]:
                        if ruth_start < end and ruth_start + timedelta(minutes=meeting_duration) > start:
                            # Check if Ruth has any other conflicts on the same day
                            for ruth_end in ruth_schedule[day]:
                                if ruth_end > start and ruth_end <= end:
                                    continue
                            # Check if Ruth has any preferences for not meeting after 13:30
                            if day == 'Wednesday' and end > datetime.strptime('13:30', '%H:%M'):
                                continue
                            # Check if the meeting time is within the work hours
                            if start < end and end <= end_time:
                                # Return the meeting time
                                return day, start.strftime('%H:%M') + '-' + end.strftime('%H:%M')

    # If no suitable time is found, return None
    return None


# Define the schedules and preferences
nicole_schedule = {
    'Monday': ['09:00-09:30', '13:00-13:30', '14:30-15:30'],
    'Tuesday': ['09:00-09:30', '11:30-13:30', '14:30-15:30'],
    'Wednesday': ['10:00-11:00', '12:30-15:00', '16:00-17:00']
}

ruth_schedule = {
    'Monday': ['09:00-17:00'],
    'Tuesday': ['09:00-17:00'],
    'Wednesday': ['09:00-10:30', '11:00-11:30', '12:00-12:30', '13:30-15:30', '16:00-16:30']
}

meeting_duration = 30
preferences = ['Monday', 'Tuesday', 'Wednesday']

# Find a suitable time for the meeting
result = find_meeting_time(nicole_schedule, ruth_schedule, meeting_duration, preferences)

# Print the result
if result:
    day, time = result
    print(f'{day}, {time}')
else:
    print('No suitable time found.')