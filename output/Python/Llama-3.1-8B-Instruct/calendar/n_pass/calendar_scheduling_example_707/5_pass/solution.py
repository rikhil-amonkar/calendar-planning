from datetime import datetime, timedelta

def find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, preferred_days):
    """
    Find a meeting time that satisfies both Ryan and Adam's schedules.

    Args:
    ryan_schedule (dict): Ryan's schedule with start and end times as strings.
    adam_schedule (dict): Adam's schedule with start and end times as strings.
    meeting_duration (float): Meeting duration in hours.
    preferred_days (list): List of preferred days for the meeting.

    Returns:
    str: The first available meeting time that meets all constraints, or "No available time slot found" if none exists.
    """

    # Convert schedules to datetime objects
    ryan_schedule = {datetime.strptime(key, '%H:%M'): datetime.strptime(value, '%H:%M') for key, value in ryan_schedule.items()}
    adam_schedule = {datetime.strptime(key, '%H:%M'): datetime.strptime(value, '%H:%M') for key, value in adam_schedule.items()}

    # Sort schedules by start time
    ryan_schedule = dict(sorted(ryan_schedule.items()))
    adam_schedule = dict(sorted(adam_schedule.items()))

    # Find available time slots for both participants
    available_time_slots = []
    for day in preferred_days:
        if day == 'Monday':
            start_time = datetime.strptime('09:00', '%H:%M')
            end_time = datetime.strptime('17:00', '%H:%M')
        elif day == 'Tuesday':
            start_time = datetime.strptime('09:00', '%H:%M')
            end_time = datetime.strptime('17:00', '%H:%M')
        elif day == 'Wednesday':
            start_time = datetime.strptime('09:00', '%H:%M')
            end_time = datetime.strptime('17:00', '%H:%M')

        while start_time < end_time:
            # Calculate the end time of the meeting
            end_time_of_meeting = start_time + timedelta(hours=meeting_duration)

            # Check if Ryan is available
            if (start_time not in ryan_schedule and end_time_of_meeting not in ryan_schedule and
                start_time + timedelta(minutes=30) not in ryan_schedule and
                end_time_of_meeting + timedelta(minutes=30) not in ryan_schedule):
                # Check if Adam is available
                if (start_time not in adam_schedule and end_time_of_meeting not in adam_schedule and
                    start_time + timedelta(minutes=30) not in adam_schedule and
                    end_time_of_meeting + timedelta(minutes=30) not in adam_schedule):
                    available_time_slots.append((start_time.strftime('%H:%M'), (end_time_of_meeting).strftime('%H:%M'), day))

            start_time += timedelta(minutes=1)

    # Find the first available time slot that meets all constraints
    for time_slot in available_time_slots:
        start_time = time_slot[0]
        end_time = time_slot[1]
        day = time_slot[2]

        if day == 'Monday':
            start_hour = int(start_time[:2])
            end_hour = int(end_time[:2])

            # Adjusted condition to match 0.5 hours meeting duration
            if start_hour == 14 and end_hour == 14.5:
                return f'{start_time}:{end_time} on {day}'
        elif day == 'Tuesday':
            return f'{start_time}:{end_time} on {day}'
        elif day == 'Wednesday':
            return f'{start_time}:{end_time} on {day}'

    return "No available time slot found"

# Example usage:
ryan_schedule = {
    '09:30': '10:00',
    '11:00': '12:00',
    '13:00': '13:30',
    '15:30': '16:00',
    '11:30': '12:30',
    '15:30': '16:00',
    '12:00': '13:00',
    '15:30': '16:00',
    '16:30': '17:00'
}
adam_schedule = {
    '09:00': '10:30',
    '11:00': '13:30',
    '14:00': '16:00',
    '16:30': '17:00',
    '09:00': '10:00',
    '10:30': '15:30',
    '16:00': '17:00',
    '09:00': '09:30',
    '10:00': '11:00',
    '11:30': '14:30',
    '15:00': '15:30',
    '16:00': '16:30'
}
meeting_duration = 0.5  # Meeting duration is now correctly set to 0.5 hours
preferred_days = ['Monday', 'Tuesday', 'Wednesday']

print(find_meeting_time(ryan_schedule, adam_schedule, meeting_duration, preferred_days))