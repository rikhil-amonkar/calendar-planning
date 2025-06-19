from datetime import datetime, timedelta

def find_meeting_time(megan_schedule, daniel_schedule, meeting_duration):
    """
    Find the first available time slot for a meeting between Megan and Daniel.

    Args:
        megan_schedule (dict): Megan's schedule with days as keys and lists of time slots as values.
        daniel_schedule (dict): Daniel's schedule with days as keys and lists of time slots as values.
        meeting_duration (float): The duration of the meeting in hours.

    Returns:
        str: The first available time slot for the meeting, or 'No available time slot found' if none is available.
    """

    # Define the work hours and days
    work_hours = [(9, 17), (13, 17)]
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    # Find the first available time slot for both Megan and Daniel
    for day in work_days:
        for start_hour in work_hours:
            for end_hour in work_hours:
                if (start_hour[0] == 9 and end_hour[0] == 17) or (start_hour[0] == 13 and end_hour[0] == 17):
                    # Convert the start and end hours to decimal hours
                    start_hour_decimal = (start_hour[0] + start_hour[1] / 60) if start_hour[1]!= 0 else start_hour[0]
                    end_hour_decimal = (end_hour[0] + end_hour[1] / 60) if end_hour[1]!= 0 else end_hour[0]

                    # Check if the time slot is available in Megan's schedule
                    if day in megan_schedule and any(start <= start_hour_decimal < end for start, end in megan_schedule[day]):
                        continue

                    # Check if the time slot is available in Daniel's schedule
                    if day in daniel_schedule and any(start <= start_hour_decimal < end for start, end in daniel_schedule[day]):
                        continue

                    # Check if the time slot is long enough to accommodate the meeting duration
                    if end_hour_decimal - start_hour_decimal >= meeting_duration:
                        # Convert the start and end hours back to integer hours
                        start_hour_integer = (int(start_hour_decimal), int((start_hour_decimal - int(start_hour_decimal)) * 60))
                        end_hour_integer = (int(end_hour_decimal), int((end_hour_decimal - int(end_hour_decimal)) * 60))

                        # Convert the time slots back to string format
                        start_hour_string = f'{start_hour_integer[0]:02d}:{start_hour_integer[1]:02d}'
                        end_hour_string = f'{end_hour_integer[0]:02d}:{end_hour_integer[1]:02d}'

                        return f'{day}, {start_hour_string} - {end_hour_string}'

    # If no available time slot is found, return a message
    return 'No available time slot found'

# Define the schedules for Megan and Daniel
megan_schedule = {
    'Monday': [(13, 13.5), (14, 15.5)],
    'Tuesday': [(9, 9.5), (12, 12.5), (16, 17)],
    'Wednesday': [(9.5, 10), (10.5, 11.5), (12.5, 14), (16, 16.5)],
    'Thursday': [(13.5, 14.5), (15, 15.5)]
}

daniel_schedule = {
    'Monday': [(10, 11.5), (12.5, 15), (12.5, 15)],
    'Tuesday': [(9, 10), (10.5, 17), (9, 10), (10.5, 17)],
    'Wednesday': [(9, 10), (10.5, 11.5), (12, 17), (9, 10), (10.5, 11.5), (12, 17)],
    'Thursday': [(9, 12), (12.5, 14.5), (15, 15.5), (9, 12), (12.5, 14.5), (15, 15.5)]
}

# Define the meeting duration
meeting_duration = 1

# Find the meeting time
meeting_time = find_meeting_time(megan_schedule, daniel_schedule, meeting_duration)
print(meeting_time)