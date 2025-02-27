from datetime import datetime, timedelta

def find_meeting_time(busy_times):
    """
    Find the earliest available half-hour time slot on Monday.

    Args:
    busy_times (list): A list of tuples representing Patrick's busy times.

    Returns:
    tuple: The start and end times of the available half-hour time slot.
    """
    # Define the start and end of the workday
    start_of_day = datetime.strptime('09:00', '%H:%M')
    end_of_day = datetime.strptime('17:00', '%H:%M')

    # Initialize the current time to the start of the day
    current_time = start_of_day

    # Iterate over the busy times
    for busy_start, busy_end in busy_times:
        # Convert the busy times to datetime objects
        busy_start = datetime.strptime(busy_start, '%H:%M')
        busy_end = datetime.strptime(busy_end, '%H:%M')

        # Check if there's a gap between the current time and the busy time
        if current_time < busy_start:
            # Calculate the end time of the available slot
            available_end = min(busy_start, current_time + timedelta(minutes=30))

            # Check if the available slot is half an hour long
            if available_end - current_time == timedelta(minutes=30):
                return (current_time.strftime('%H:%M'), available_end.strftime('%H:%M'))

        # Move to the end of the busy time
        current_time = busy_end

    # Check if there's a gap between the last busy time and the end of the day
    if current_time < end_of_day:
        # Calculate the end time of the available slot
        available_end = min(end_of_day, current_time + timedelta(minutes=30))

        # Check if the available slot is half an hour long
        if available_end - current_time == timedelta(minutes=30):
            return (current_time.strftime('%H:%M'), available_end.strftime('%H:%M'))

    # If no available slot is found, return None
    return None


# Define Patrick's busy times
busy_times = [
    ('09:00', '09:30'),
    ('10:30', '12:00'),
    ('12:30', '13:30'),
    ('14:00', '14:30'),
    ('15:00', '16:30')
]

# Find the available time slot
available_time = find_meeting_time(busy_times)

if available_time:
    print(f'The meeting can be scheduled from {available_time[0]} to {available_time[1]}.')
else:
    print('No available time slot found.')
    