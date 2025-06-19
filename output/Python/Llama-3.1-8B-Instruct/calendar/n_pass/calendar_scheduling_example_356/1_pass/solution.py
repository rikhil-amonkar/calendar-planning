from datetime import datetime, timedelta

def find_meeting_time(schedules, meeting_duration, preferences=None):
    # Sort schedules by start time
    schedules.sort(key=lambda x: x[0])

    # Initialize the current time
    current_time = datetime.strptime('09:00', '%H:%M')

    # Iterate over the schedules
    for start, end in schedules:
        # Convert times to datetime objects
        start = datetime.strptime(start, '%H:%M')
        end = datetime.strptime(end, '%H:%M')

        # Check if the current time is within the schedule
        if start <= current_time < end:
            # If the current time is before the schedule, move to the end of the schedule
            current_time = end

    # Check if the current time is after the work hours
    if current_time > datetime.strptime('17:00', '%H:%M'):
        current_time = datetime.strptime('17:00', '%H:%M')

    # Add the meeting duration to the current time
    end_time = current_time + timedelta(hours=meeting_duration)

    # Check if the end time is before the work hours
    if end_time < datetime.strptime('09:00', '%H:%M'):
        end_time = datetime.strptime('09:00', '%H:%M') + timedelta(hours=meeting_duration)

    # Return the time range and day of the week
    return f"{current_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {current_time.strftime('%A')}"


# Define the schedules
schedules = [
    ('12:00', '12:30'),
    ('13:00', '14:30'),
    ('09:00', '09:30'),
    ('10:30', '11:00'),
    ('13:30', '14:00'),
    ('15:00', '15:30'),
    ('09:00', '10:00'),
    ('10:30', '11:00'),
    ('11:30', '14:00'),
    ('14:30', '15:00'),
    ('16:30', '17:00'),
    ('09:30', '11:00'),
    ('11:30', '13:30'),
    ('14:00', '16:00'),
    ('16:30', '17:00'),
    ('09:00', '11:00'),
    ('11:30', '12:30'),
    ('13:00', '14:30'),
    ('15:00', '16:00'),
    ('16:30', '17:00')
]

# Define the meeting duration
meeting_duration = 0.5

# Define the preferences
preferences = [
    {'name': 'Angela', 'preference': 'avoid before 15:00'}
]

# Find the meeting time
print(find_meeting_time(schedules, meeting_duration, preferences))