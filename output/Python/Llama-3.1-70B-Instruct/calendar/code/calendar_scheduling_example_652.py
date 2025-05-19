from datetime import datetime, timedelta

def find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_hours, days):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    jesse_schedule (list): Jesse's existing schedule.
    lawrence_schedule (list): Lawrence's existing schedule.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): The work hours.
    days (list): The possible days for the meeting.

    Returns:
    tuple: A tuple containing the proposed meeting time and day.
    """

    # Convert the work hours to datetime objects
    start_time = datetime.strptime(work_hours[0], '%H:%M')
    end_time = datetime.strptime(work_hours[1], '%H:%M')

    # Iterate over each day
    for day in days:
        # Initialize the current time to the start of the work hours
        current_time = start_time

        # Iterate until we reach the end of the work hours
        while current_time < end_time:
            # Check if Jesse and Lawrence are both available at the current time
            if (not is_busy(jesse_schedule, current_time, meeting_duration, day) and
                    not is_busy(lawrence_schedule, current_time, meeting_duration, day)):
                # If Lawrence can't meet after 16:30 on Tuesday, skip this time
                if day == 'Tuesday' and current_time.hour >= 16 and current_time.minute >= 30:
                    current_time += timedelta(minutes=30)
                    continue

                # Calculate the end time of the meeting
                end_meeting_time = current_time + timedelta(minutes=meeting_duration)

                # Format the meeting time as HH:MM-HH:MM
                meeting_time = f"{current_time.strftime('%H:%M')}-{end_meeting_time.strftime('%H:%M')}"

                # Return the proposed meeting time and day
                return meeting_time, day

            # Move to the next time slot
            current_time += timedelta(minutes=30)

    # If no suitable time is found, return None
    return None


def is_busy(schedule, current_time, meeting_duration, day):
    """
    Check if a person is busy at a given time.

    Args:
    schedule (list): The person's existing schedule.
    current_time (datetime): The current time.
    meeting_duration (int): The duration of the meeting in minutes.
    day (str): The day of the week.

    Returns:
    bool: True if the person is busy, False otherwise.
    """

    # Iterate over each scheduled meeting
    for scheduled_meeting in schedule:
        # Check if the scheduled meeting is on the same day
        if scheduled_meeting['day'] == day:
            # Convert the scheduled meeting time to datetime objects
            start_scheduled_meeting = datetime.strptime(scheduled_meeting['start'], '%H:%M')
            end_scheduled_meeting = datetime.strptime(scheduled_meeting['end'], '%H:%M')

            # Check if the current time overlaps with the scheduled meeting
            if (current_time >= start_scheduled_meeting and
                    current_time + timedelta(minutes=meeting_duration) <= end_scheduled_meeting):
                return True

    # If no overlap is found, return False
    return False


# Jesse's existing schedule
jesse_schedule = [
    {'day': 'Monday','start': '13:30', 'end': '14:00'},
    {'day': 'Monday','start': '14:30', 'end': '15:00'},
    {'day': 'Tuesday','start': '09:00', 'end': '09:30'},
    {'day': 'Tuesday','start': '13:00', 'end': '13:30'},
    {'day': 'Tuesday','start': '14:00', 'end': '15:00'}
]

# Lawrence's existing schedule
lawrence_schedule = [
    {'day': 'Monday','start': '09:00', 'end': '17:00'},
    {'day': 'Tuesday','start': '09:30', 'end': '10:30'},
    {'day': 'Tuesday','start': '11:30', 'end': '12:30'},
    {'day': 'Tuesday','start': '13:00', 'end': '13:30'},
    {'day': 'Tuesday','start': '14:30', 'end': '15:00'},
    {'day': 'Tuesday','start': '15:30', 'end': '16:30'}
]

# Meeting duration in minutes
meeting_duration = 30

# Work hours
work_hours = ('09:00', '17:00')

# Possible days for the meeting
days = ['Monday', 'Tuesday']

# Find a suitable time for the meeting
meeting_time, day = find_meeting_time(jesse_schedule, lawrence_schedule, meeting_duration, work_hours, days)

# Print the proposed meeting time and day
print(f"Proposed meeting time: {meeting_time} on {day}")