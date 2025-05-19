from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, days):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary where the keys are the participants' names and the values are dictionaries with days as keys and lists of tuples representing their busy time ranges as values.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the work hours (start, end) in minutes.
    days (list): A list of days of the week.

    Returns:
    tuple: A tuple representing the proposed meeting time range (start, end) in minutes and the day of the week.
    """

    # Convert work hours to minutes
    work_start = work_hours[0].split(':')
    work_start_minutes = int(work_start[0]) * 60 + int(work_start[1])
    work_end = work_hours[1].split(':')
    work_end_minutes = int(work_end[0]) * 60 + int(work_end[1])

    # Initialize the proposed meeting time range
    proposed_time = None

    # Iterate over the days
    for day in days:
        # Iterate over the possible time ranges
        for time in range(work_start_minutes, work_end_minutes - meeting_duration + 1):
            # Assume the current time range is available
            is_available = True

            # Check if the current time range is available for all participants
            for participant, schedule in participants.items():
                if day in schedule:
                    for busy_time in schedule[day]:
                        busy_start = busy_time[0].split(':')
                        busy_start_minutes = int(busy_start[0]) * 60 + int(busy_start[1])
                        busy_end = busy_time[1].split(':')
                        busy_end_minutes = int(busy_end[0]) * 60 + int(busy_end[1])

                        # If the current time range overlaps with a busy time range, it's not available
                        if (time >= busy_start_minutes and time < busy_end_minutes) or (time + meeting_duration > busy_start_minutes and time + meeting_duration <= busy_end_minutes):
                            is_available = False
                            break

                    # If the current time range is not available, break the loop
                    if not is_available:
                        break

            # If the current time range is available, propose it
            if is_available:
                proposed_time = (time, time + meeting_duration)
                break

        # If a proposed time is found, break the loop
        if proposed_time:
            break

    # Convert the proposed meeting time range to HH:MM format
    proposed_time_start = datetime.strptime(str(proposed_time[0] // 60) + ':' + str(proposed_time[0] % 60), '%H:%M')
    proposed_time_end = datetime.strptime(str(proposed_time[1] // 60) + ':' + str(proposed_time[1] % 60), '%H:%M')

    return proposed_time_start.strftime('%H:%M') + '-' + proposed_time_end.strftime('%H:%M'), day


# Define the participants' schedules
participants = {
    'Natalie': {
        'Monday': [('9:00', '9:30'), ('10:00', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:30')],
        'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('12:30', '14:00'), ('16:00', '17:00')],
        'Wednesday': [('11:00', '11:30'), ('16:00', '16:30')],
        'Thursday': [('10:00', '11:00'), ('11:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')]
    },
    'William': {
        'Monday': [('9:30', '11:00'), ('11:30', '17:00')],
        'Tuesday': [('9:00', '13:00'), ('13:30', '16:00')],
        'Wednesday': [('9:00', '12:30'), ('13:00', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')],
        'Thursday': [('9:00', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '14:00'), ('15:00', '17:00')]
    }
}

# Define the meeting duration, work hours, and days
meeting_duration = 60
work_hours = ('9:00', '17:00')
days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

# Find a suitable time for the meeting
proposed_time, day = find_meeting_time(participants, meeting_duration, work_hours, days)

print(f'Proposed meeting time: {proposed_time} on {day}')