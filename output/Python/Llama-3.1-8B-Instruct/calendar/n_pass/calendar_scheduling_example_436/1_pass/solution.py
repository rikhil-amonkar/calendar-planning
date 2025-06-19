from datetime import datetime, timedelta

def find_available_time(participants, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    participants (dict): A dictionary where keys are participant names and values are lists of their busy times.
    meeting_duration (int): The duration of the meeting in minutes.

    Returns:
    tuple: A tuple containing the start and end times of the meeting in the format HH:MM and the day of the week.
    """
    # Find the earliest start time on Monday
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Find the latest end time on Monday
    latest_end_time = datetime.strptime('17:00', '%H:%M')

    # Sort the busy times for each participant
    for participant in participants:
        participants[participant].sort()

    # Iterate over the possible start times
    while start_time < end_time:
        # Check if the meeting can be scheduled at the current start time
        can_schedule = True
        for participant in participants:
            for i in range(len(participants[participant]) - 1):
                # Check if the meeting conflicts with any of the participant's busy times
                if (participants[participant][i] <= start_time + timedelta(minutes=meeting_duration) < participants[participant][i+1]) or \
                   (start_time < participants[participant][i] < start_time + timedelta(minutes=meeting_duration)) or \
                   (participants[participant][i] < start_time + timedelta(minutes=meeting_duration) < participants[participant][i+1]):
                    can_schedule = False
                    break
            if not can_schedule:
                break
        if can_schedule:
            # If the meeting can be scheduled, return the start and end times
            end_time = start_time + timedelta(minutes=meeting_duration)
            return start_time.strftime('%H:%M'), end_time.strftime('%H:%M'), 'Monday'

        # If the meeting cannot be scheduled, try the next start time
        start_time += timedelta(minutes=1)

        # If the next start time is after the latest end time, try the next day
        if start_time > end_time:
            start_time = datetime.strptime('09:00', '%H:%M')
            end_time = datetime.strptime('17:00', '%H:%M')
            latest_end_time = datetime.strptime('17:00', '%H:%M')
            participants['Angela'].append(datetime.strptime('12:30', '%H:%M').replace(year=2024, month=7, day=22))
            participants['Angela'].append(datetime.strptime('15:00', '%H:%M').replace(year=2024, month=7, day=22))
            participants['Angela'].append(datetime.strptime('15:30', '%H:%M').replace(year=2024, month=7, day=22))
            participants['Angela'].append(datetime.strptime('16:30', '%H:%M').replace(year=2024, month=7, day=22))
            participants['Angela'].sort()

    # If no available time is found, return None
    return None

# Define the busy times for each participant
participants = {
    'Patrick': [datetime.strptime('13:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('14:00', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('14:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('15:00', '%H:%M').replace(year=2024, month=7, day=22)],
    'Shirley': [datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('09:30', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('11:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('11:30', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('12:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('12:30', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('14:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('15:00', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('16:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('17:00', '%H:%M').replace(year=2024, month=7, day=22)],
    'Jeffrey': [datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('09:30', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('10:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('11:00', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('11:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('13:00', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('13:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('16:00', '%H:%M').replace(year=2024, month=7, day=22),
                datetime.strptime('17:00', '%H:%M').replace(year=2024, month=7, day=22)],
    'Gloria': [datetime.strptime('11:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('12:00', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('15:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('15:30', '%H:%M').replace(year=2024, month=7, day=22)],
    'Nathan': [datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('09:30', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('10:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('12:00', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('14:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('17:00', '%H:%M').replace(year=2024, month=7, day=22)],
    'Angela': [datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('09:30', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('10:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('11:00', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('12:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('15:00', '%H:%M').replace(year=2024, month=7, day=22),
               datetime.strptime('15:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('16:30', '%H:%M').replace(year=2024, month=7, day=22)],
    'David': [datetime.strptime('09:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('09:30', '%H:%M').replace(year=2024, month=7, day=22),
              datetime.strptime('10:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('10:30', '%H:%M').replace(year=2024, month=7, day=22),
              datetime.strptime('11:00', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('14:00', '%H:%M').replace(year=2024, month=7, day=22),
              datetime.strptime('14:30', '%H:%M').replace(year=2024, month=7, day=22), datetime.strptime('16:30', '%H:%M').replace(year=2024, month=7, day=22)]
}

# Define the meeting duration
meeting_duration = 30

# Find the available time
available_time = find_available_time(participants, meeting_duration)

# Print the available time
if available_time:
    print(f"Available time: {available_time[0]}-{available_time[1]} on {available_time[2]}")
else:
    print("No available time found.")