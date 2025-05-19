from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    - participants (dict): A dictionary where the keys are the participant names and the values are lists of tuples representing their busy times.
    - meeting_duration (int): The duration of the meeting in minutes.
    - work_hours (tuple): A tuple representing the start and end times of the work hours.

    Returns:
    - A tuple containing the proposed meeting time and day.
    """

    # Define the days of the week
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Iterate over each day
    for day in days:
        # Initialize the start time to the beginning of the work hours
        start_time = work_hours[0]

        # Iterate until we find a suitable time or we reach the end of the work hours
        while start_time < work_hours[1]:
            # Calculate the end time of the proposed meeting
            end_time = start_time + timedelta(minutes=meeting_duration)

            # Assume the proposed time is suitable for all participants
            is_suitable = True

            # Check if the proposed time is suitable for each participant
            for participant, busy_times in participants.items():
                # Check if the proposed time overlaps with any of the participant's busy times
                for busy_start, busy_end in busy_times:
                    if (start_time >= busy_start and start_time < busy_end) or (end_time > busy_start and end_time <= busy_end):
                        # If the proposed time overlaps, it's not suitable
                        is_suitable = False
                        break

                # If we've already determined the proposed time is not suitable, we can move on to the next participant
                if not is_suitable:
                    break

            # If the proposed time is suitable for all participants, return it
            if is_suitable:
                return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}", day

            # If the proposed time is not suitable, move on to the next time slot
            start_time += timedelta(minutes=30)

    # If we've iterated over all time slots and haven't found a suitable time, return None
    return None

# Define the participants' schedules
participants = {
    'Robert': {
        'Monday': [
            (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
            (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
        ],
        'Tuesday': [
            (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
            (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
        ],
        'Wednesday': [
            (datetime.strptime('10:00', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
            (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
            (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
            (datetime.strptime('13:30', '%H:%M'), datetime.strptime('14:00', '%H:%M')),
            (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
            (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M')),
        ]
    },
    'Ralph': {
        'Monday': [
            (datetime.strptime('10:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
            (datetime.strptime('15:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        ],
        'Tuesday': [
            (datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
            (datetime.strptime('10:00', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
            (datetime.strptime('11:00', '%H:%M'), datetime.strptime('11:30', '%H:%M')),
            (datetime.strptime('12:00', '%H:%M'), datetime.strptime('13:00', '%H:%M')),
            (datetime.strptime('14:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
            (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        ],
        'Wednesday': [
            (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
            (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
            (datetime.strptime('13:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
            (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M')),
        ]
    }
}

work_hours = (datetime.strptime('09:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))
meeting_duration = 30

# Find a suitable meeting time
meeting_time, day = find_meeting_time(participants, meeting_duration, work_hours)

# Print the result
print(f"Proposed meeting time: {meeting_time} on {day}")