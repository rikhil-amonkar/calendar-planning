from datetime import datetime, timedelta

def find_available_time(ronald_schedule, amber_schedule, meeting_duration):
    """
    Find the earliest available time for a meeting between Ronald and Amber.
    
    Args:
    ronald_schedule (dict): Ronald's schedule with time slots as keys and availability as values.
    amber_schedule (dict): Amber's schedule with time slots as keys and availability as values.
    meeting_duration (int): The duration of the meeting in minutes.
    
    Returns:
    tuple: A tuple containing the day of the week, start time, and end time of the meeting.
    """
    
    # Define the work hours and days
    work_hours = range(9, 18)
    work_days = ['Monday', 'Tuesday', 'Wednesday']
    
    # Initialize the earliest available time
    earliest_time = None
    
    # Iterate over each day
    for day in work_days:
        # Initialize the current time
        current_time = datetime.strptime(f'{day} 09:00', '%A %H:%M')
        
        # Iterate until we find an available time or the end of the day
        while current_time.time() < datetime.strptime('17:00', '%H:%M').time():
            # Check if the current time is available for both Ronald and Amber
            if (current_time.time() not in [t.time() for t in ronald_schedule]) and (current_time.time() not in [t.time() for t in amber_schedule]):
                # Check if the meeting can fit in the current time slot
                if (current_time + timedelta(minutes=meeting_duration)).time() <= datetime.strptime('17:00', '%H:%M').time():
                    # Update the earliest available time
                    if earliest_time is None or current_time < earliest_time:
                        earliest_time = current_time
                        break
            # Move to the next time slot
            current_time += timedelta(minutes=30)
    
    # Return the earliest available time
    if earliest_time is not None:
        return earliest_time.strftime('%A %H:%M'), (earliest_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')
    else:
        return None

# Define the schedules
ronald_schedule = {
    datetime.strptime('Monday 10:30', '%A %H:%M'): True,
    datetime.strptime('Monday 12:00', '%A %H:%M'): True,
    datetime.strptime('Monday 15:30', '%A %H:%M'): True,
    datetime.strptime('Tuesday 09:00', '%A %H:%M'): True,
    datetime.strptime('Tuesday 12:00', '%A %H:%M'): True,
    datetime.strptime('Tuesday 15:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 09:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 11:00', '%A %H:%M'): True,
    datetime.strptime('Wednesday 12:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 13:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 16:30', '%A %H:%M'): True,
}

amber_schedule = {
    datetime.strptime('Monday 09:00', '%A %H:%M'): True,
    datetime.strptime('Monday 10:00', '%A %H:%M'): True,
    datetime.strptime('Monday 11:30', '%A %H:%M'): True,
    datetime.strptime('Monday 12:30', '%A %H:%M'): True,
    datetime.strptime('Monday 14:00', '%A %H:%M'): True,
    datetime.strptime('Monday 14:30', '%A %H:%M'): True,
    datetime.strptime('Monday 15:30', '%A %H:%M'): True,
    datetime.strptime('Tuesday 09:00', '%A %H:%M'): True,
    datetime.strptime('Tuesday 10:00', '%A %H:%M'): True,
    datetime.strptime('Tuesday 12:00', '%A %H:%M'): True,
    datetime.strptime('Tuesday 13:30', '%A %H:%M'): True,
    datetime.strptime('Tuesday 15:30', '%A %H:%M'): True,
    datetime.strptime('Tuesday 16:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 09:00', '%A %H:%M'): True,
    datetime.strptime('Wednesday 10:00', '%A %H:%M'): True,
    datetime.strptime('Wednesday 11:00', '%A %H:%M'): True,
    datetime.strptime('Wednesday 13:30', '%A %H:%M'): True,
    datetime.strptime('Wednesday 15:00', '%A %H:%M'): True,
    datetime.strptime('Wednesday 15:30', '%A %H:%M'): True,
}

# Define the meeting duration
meeting_duration = 30

# Find the available time
available_time = find_available_time(ronald_schedule, amber_schedule, meeting_duration)

# Print the result
if available_time:
    day, start_time = available_time
    print(f'{start_time} {day}')
else:
    print('No available time found.')