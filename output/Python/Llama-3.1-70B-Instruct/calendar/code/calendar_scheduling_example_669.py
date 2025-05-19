from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, days, preferences=None):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary of participants with their existing schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the start and end time of work hours.
    days (list): A list of days of the week.
    preferences (dict): A dictionary of participants with their time preferences.

    Returns:
    str: A string representing the proposed meeting time in the format HH:MM:HH:MM and the day of the week.
    """

    # Loop through each day
    for day in days:
        # Convert work hours to datetime objects
        start_time = datetime.strptime(work_hours[0], '%H:%M')
        end_time = datetime.strptime(work_hours[1], '%H:%M')

        # Initialize the current time to the start of work hours
        current_time = start_time

        # Loop through each minute of the work hours
        while current_time < end_time:
            # Check if the current time slot is available for all participants
            if is_time_slot_available(participants, current_time, meeting_duration, day):
                # Check if the current time slot meets the preferences of all participants
                if preferences is not None and not is_time_slot_preferred(preferences, current_time, day):
                    # If not preferred, move to the next minute
                    current_time += timedelta(minutes=1)
                    continue
                # If available and preferred, return the proposed meeting time
                proposed_time = current_time.strftime('%H:%M') + ':' + (current_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')
                return proposed_time + ',' + day
            # If not available, move to the next minute
            current_time += timedelta(minutes=1)

def is_time_slot_available(participants, start_time, duration, day):
    """
    Check if a time slot is available for all participants.

    Args:
    participants (dict): A dictionary of participants with their existing schedules.
    start_time (datetime): The start time of the time slot.
    duration (int): The duration of the time slot in minutes.
    day (str): The day of the week.

    Returns:
    bool: True if the time slot is available for all participants, False otherwise.
    """

    # Loop through each participant's schedule
    for participant, schedule in participants.items():
        # Check if the participant has a schedule for the given day
        if day in schedule:
            # Loop through each time slot in the participant's schedule
            for time_slot in schedule[day]:
                # Convert the time slot to datetime objects
                time_slot_start = datetime.strptime(time_slot[0], '%H:%M')
                time_slot_end = datetime.strptime(time_slot[1], '%H:%M')

                # Check if the proposed time slot overlaps with the participant's schedule
                if (start_time >= time_slot_start and start_time < time_slot_end) or (start_time + timedelta(minutes=duration) > time_slot_start and start_time + timedelta(minutes=duration) <= time_slot_end):
                    # If overlapping, return False
                    return False
    # If no overlapping time slots found, return True
    return True

def is_time_slot_preferred(preferences, start_time, day):
    """
    Check if a time slot meets the preferences of all participants.

    Args:
    preferences (dict): A dictionary of participants with their time preferences.
    start_time (datetime): The start time of the time slot.
    day (str): The day of the week.

    Returns:
    bool: True if the time slot meets the preferences of all participants, False otherwise.
    """

    # Loop through each participant's preferences
    for participant, preference in preferences.items():
        # Check if the start time meets the participant's preference
        if preference['day'] == day and preference['end_time'] is not None and start_time > datetime.strptime(preference['end_time'], '%H:%M'):
            # If not preferred, return False
            return False
    # If all preferences met, return True
    return True

# Define the participants' schedules
participants = {
    'Jean': {
        'Tuesday': [('11:30', '12:00'), ('16:00', '16:30')]
    },
    'Doris': {
        'Monday': [('09:00', '11:30'), ('12:00', '12:30'), ('13:30', '16:00'), ('16:30', '17:00')],
        'Tuesday': [('09:00', '17:00')]
    }
}

# Define the meeting duration and work hours
meeting_duration = 30
work_hours = ('09:00', '17:00')

# Define the days of the week
days = ['Monday', 'Tuesday']

# Define the participants' preferences
preferences = {
    'Doris': {'day': 'Monday', 'end_time': '14:00'}
}

# Find the proposed meeting time
proposed_time = find_meeting_time(participants, meeting_duration, work_hours, days, preferences)

print(proposed_time)