def find_best_availability(start_time, end_time, busy_times):
    """
    Find the best availability for scheduling a meeting.

    Args:
    start_time (int): The start time of the work hours in minutes.
    end_time (int): The end time of the work hours in minutes.
    busy_times (list): A list of busy times in minutes.

    Returns:
    str: The proposed time for the meeting in the format 'Day, HH:MM - HH:MM'.
    """
    # Convert busy times to minutes
    busy_times = [time for time in busy_times if start_time <= time <= end_time]

    # Sort busy times
    busy_times.sort()

    # Initialize the best availability
    best_availability = None

    # Iterate over the possible meeting times
    for hour in range(start_time, end_time):
        # Check if the current time is available
        if hour not in busy_times:
            # Check if the next half hour is available
            next_half_hour = hour + 30
            if next_half_hour not in busy_times:
                # Update the best availability
                if best_availability is None or hour < best_availability[0]:
                    best_availability = (hour, next_half_hour)

    # Convert the best availability to a string
    if best_availability is not None:
        day = 'Monday'
        start_hour = best_availability[0] // 60
        start_minute = best_availability[0] % 60
        end_hour = best_availability[1] // 60
        end_minute = best_availability[1] % 60
        return f'{day}, {start_hour}:{start_minute:02d} - {end_hour}:{end_minute:02d}'
    else:
        return 'No available time found'

# Define the busy times for Patrick
busy_times = [90, 210, 330, 420, 450, 540, 630]

# Define the start and end times of the work hours
start_time = 90
end_time = 630

# Find the best availability
proposed_time = find_best_availability(start_time, end_time, busy_times)

# Print the proposed time
print(f'Here is the proposed time: {proposed_time}')
