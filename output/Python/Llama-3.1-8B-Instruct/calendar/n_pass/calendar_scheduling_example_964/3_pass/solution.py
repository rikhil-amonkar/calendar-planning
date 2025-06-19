from datetime import datetime, timedelta

def schedule_meeting(betty_schedule, megan_schedule, duration, excluded_days):
    # Define work hours
    start_hour = 9
    end_hour = 17

    # Validate the meeting duration
    if not isinstance(duration, int) or duration <= 0:
        raise ValueError("Meeting duration must be a positive integer")

    # Initialize variables to store the result
    result = None
    result_day = None

    # Iterate over each day
    for day in ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']:
        # Initialize a flag to check if a meeting can be scheduled for the day
        can_schedule = True

        # Iterate over each hour in the work hours
        for hour in range(start_hour, end_hour):
            # Initialize a flag to check if the hour is available for both participants
            is_available = True

            # Check if the hour is available for Betty
            for time in betty_schedule[day]:
                start_time = datetime.strptime(time, '%H:%M')
                end_time = start_time + timedelta(minutes=30)
                if start_time <= datetime(f'{hour:02d}', '%H') <= end_time:
                    is_available = False
                    break

            # Check if the hour is available for Megan
            for time in megan_schedule[day]:
                start_time = datetime.strptime(time, '%H:%M')
                end_time = start_time + timedelta(minutes=30)
                if start_time <= datetime(f'{hour:02d}', '%H') <= end_time:
                    is_available = False
                    break

            # Check if the hour is within the excluded days
            if day in excluded_days:
                is_available = False

            # If the hour is available, check if it can accommodate the meeting duration
            if is_available:
                start_time = datetime(f'{hour:02d}', '%H')
                end_time = start_time + timedelta(hours=duration)
                if end_time.hour <= end_hour:
                    # If a meeting can be scheduled for the day, store the result
                    result = f'{hour:02d}:{60 if hour < 12 else 0} - {(hour + duration):02d}:{60 if (hour + duration) < 12 else 0}'
                    result_day = day
                    can_schedule = False
                    break

        # If a meeting can be scheduled for the day, break the loop
        if not can_schedule:
            break

    # Return the result
    if result:
        return f'{result} on {result_day}'
    else:
        return 'No meeting time available'

# Define the schedules
betty_schedule = {
    'Monday': ['10:00', '10:30', '11:30', '12:30', '16:00', '16:30'],
    'Tuesday': ['9:30', '10:00', '10:30', '12:00', '12:30', '13:30', '15:00', '16:30', '17:00'],
    'Wednesday': ['13:30', '14:00', '14:30', '15:00'],
    'Thursday': [],
    'Friday': ['9:00', '10:00', '11:30', '12:00', '12:30', '13:00', '14:30', '15:00']
}

megan_schedule = {
    'Monday': ['9:00', '9:30', '10:00', '10:30', '12:00', '14:00', '15:00', '15:30', '16:00', '16:30', '17:00'],
    'Tuesday': ['9:00', '9:30', '10:00', '10:30', '12:00', '14:00', '15:00', '15:30', '16:00', '16:30'],
    'Wednesday': ['9:30', '10:30', '11:00', '11:30', '12:30', '13:00', '13:30', '14:30', '15:30', '17:00'],
    'Thursday': ['9:00', '10:30', '11:30', '14:00', '14:30', '15:00', '15:30', '16:30'],
    'Friday': ['9:00', '9:30', '10:00', '10:30', '11:30', '12:00', '12:30', '13:00', '14:30', '15:00', '17:00']
}

# Define the excluded days
excluded_days = ['Wednesday', 'Thursday']

# Define the meeting duration
duration = 1

# Call the function to schedule the meeting
print(schedule_meeting(betty_schedule, megan_schedule, duration, excluded_days))