from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, day):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary of participants with their existing schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the start and end time of work hours.
    day (str): The day of the week.

    Returns:
    str: A string representing the proposed meeting time in the format HH:MM:HH:MM and the day of the week.
    """

    # Convert work hours to datetime objects
    start_time = datetime.strptime(work_hours[0], '%H:%M')
    end_time = datetime.strptime(work_hours[1], '%H:%M')

    # Initialize the current time to the start of work hours
    current_time = start_time

    # Loop through each minute of the work hours
    while current_time < end_time:
        # Check if the current time slot is available for all participants
        if is_time_slot_available(participants, current_time, meeting_duration):
            # If available, return the proposed meeting time
            proposed_time = current_time.strftime('%H:%M') + ':' + (current_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')
            return proposed_time + ','+ day
        # If not available, move to the next minute
        current_time += timedelta(minutes=1)

def is_time_slot_available(participants, start_time, duration):
    """
    Check if a time slot is available for all participants.

    Args:
    participants (dict): A dictionary of participants with their existing schedules.
    start_time (datetime): The start time of the time slot.
    duration (int): The duration of the time slot in minutes.

    Returns:
    bool: True if the time slot is available for all participants, False otherwise.
    """

    # Loop through each participant's schedule
    for participant, schedule in participants.items():
        # Loop through each time slot in the participant's schedule
        for time_slot in schedule:
            # Convert the time slot to datetime objects
            time_slot_start = datetime.strptime(time_slot[0], '%H:%M')
            time_slot_end = datetime.strptime(time_slot[1], '%H:%M')

            # Check if the proposed time slot overlaps with the participant's schedule
            if (start_time >= time_slot_start and start_time < time_slot_end) or (start_time + timedelta(minutes=duration) > time_slot_start and start_time + timedelta(minutes=duration) <= time_slot_end):
                # If overlapping, return False
                return False
    # If no overlapping time slots found, return True
    return True

# Define the participants' schedules
participants = {
    'Joe': [('09:30', '10:00'), ('10:30', '11:00')],
    'Keith': [('11:30', '12:00'), ('15:00', '15:30')],
    'Patricia': [('09:00', '09:30'), ('13:00', '13:30')],
    'Nancy': [('09:00', '11:00'), ('11:30', '16:30')],
    'Pamela': [('09:00', '10:00'), ('10:30', '11:00'), ('11:30', '12:30'), ('13:00', '14:00'), ('14:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')]
}

# Define the meeting duration and work hours
meeting_duration = 30
work_hours = ('09:00', '17:00')

# Define the day of the week
day = 'Monday'

# Find the proposed meeting time
proposed_time = find_meeting_time(participants, meeting_duration, work_hours, day)

print(proposed_time)