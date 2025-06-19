from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules, duration=30):
    """
    Find a time slot that works for all participants.

    Args:
    start_time (datetime): The start time of the meeting.
    end_time (datetime): The end time of the meeting.
    schedules (dict): A dictionary where keys are participant names and values are their schedules.
    duration (int): The duration of the time slot in minutes.

    Returns:
    tuple: A tuple containing the start time and end time of the meeting if found, otherwise None.
    """
    # Check if the start time is before the end time
    if start_time >= end_time:
        return None

    # Initialize the available time slot
    available_time = None

    # Iterate over all possible time slots
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, duration):  # Meeting duration is specified
            time = start_time.replace(hour=hour, minute=minute, second=0)

            # Check if the time slot is available for all participants
            if all(
                not (
                    time >= schedule['start']
                    and time < schedule['end']
                    or (
                        schedule['start'] < time
                        and schedule['end'] > (time + timedelta(minutes=duration))
                    )
                )
                for schedule in schedules.values()
            ):
                available_time = (time, time + timedelta(minutes=duration))
                break
            if available_time:
                break
        if available_time:
            break

    return available_time


def main():
    # Define the start and end time of the meeting
    start_time = datetime(2024, 7, 29, 8, 0, 0)  # Monday
    end_time = datetime(2024, 7, 29, 18, 0, 0)

    # Define the schedules for each participant
    schedules = {
        'Tyler': {'start': datetime(2024, 7, 29, 0, 0, 0), 'end': datetime(2024, 7, 29, 18, 0, 0)},
        'Kelly': {'start': datetime(2024, 7, 29, 0, 0, 0), 'end': datetime(2024, 7, 29, 18, 0, 0)},
        'Stephanie': [
            {'start': datetime(2024, 7, 29, 11, 0, 0), 'end': datetime(2024, 7, 29, 11, 30, 0)},
            {'start': datetime(2024, 7, 29, 14, 30, 0), 'end': datetime(2024, 7, 29, 15, 0, 0)},
        ],
        'Hannah': {'start': datetime(2024, 7, 29, 0, 0, 0), 'end': datetime(2024, 7, 29, 18, 0, 0)},
        'Joe': [
            {'start': datetime(2024, 7, 29, 9, 0, 0), 'end': datetime(2024, 7, 29, 9, 30, 0)},
            {'start': datetime(2024, 7, 29, 10, 0, 0), 'end': datetime(2024, 7, 29, 12, 0, 0)},
            {'start': datetime(2024, 7, 29, 12, 30, 0), 'end': datetime(2024, 7, 29, 13, 0, 0)},
            {'start': datetime(2024, 7, 29, 14, 0, 0), 'end': datetime(2024, 7, 29, 17, 0, 0)},
        ],
        'Diana': [
            {'start': datetime(2024, 7, 29, 9, 0, 0), 'end': datetime(2024, 7, 29, 10, 30, 0)},
            {'start': datetime(2024, 7, 29, 11, 30, 0), 'end': datetime(2024, 7, 29, 12, 0, 0)},
            {'start': datetime(2024, 7, 29, 13, 0, 0), 'end': datetime(2024, 7, 29, 14, 0, 0)},
            {'start': datetime(2024, 7, 29, 14, 30, 0), 'end': datetime(2024, 7, 29, 15, 30, 0)},
            {'start': datetime(2024, 7, 29, 16, 0, 0), 'end': datetime(2024, 7, 29, 17, 0, 0)},
        ],
        'Deborah': [
            {'start': datetime(2024, 7, 29, 9, 0, 0), 'end': datetime(2024, 7, 29, 10, 0, 0)},
            {'start': datetime(2024, 7, 29, 10, 30, 0), 'end': datetime(2024, 7, 29, 12, 0, 0)},
            {'start': datetime(2024, 7, 29, 12, 30, 0), 'end': datetime(2024, 7, 29, 13, 0, 0)},
            {'start': datetime(2024, 7, 29, 13, 30, 0), 'end': datetime(2024, 7, 29, 14, 0, 0)},
            {'start': datetime(2024, 7, 29, 14, 30, 0), 'end': datetime(2024, 7, 29, 15, 30, 0)},
            {'start': datetime(2024, 7, 29, 16, 0, 0), 'end': datetime(2024, 7, 29, 16, 30, 0)},
        ],
    }

    # Find a time slot that works for all participants
    available_time = find_available_time(start_time, end_time, schedules)

    # Print the result
    if available_time:
        start, end = available_time
        day_of_week = start.strftime('%A')
        print(f'{start.strftime("%H:%M")}-{end.strftime("%H:%M")}, {day_of_week}')
    else:
        print('No available time slot found.')

if __name__ == '__main__':
    main()