from datetime import datetime, timedelta

def find_meeting_time(martha_schedule, beverly_schedule, meeting_duration):
    """
    Find a suitable time for a meeting between Martha and Beverly.

    Args:
    martha_schedule (dict): Martha's schedule with day as key and time ranges as values.
    beverly_schedule (dict): Beverly's schedule with day as key and time ranges as values.
    meeting_duration (int): The duration of the meeting in minutes.

    Returns:
    tuple: A tuple containing the day of the week, start time, and end time of the meeting.
    """

    # Define the work hours
    work_hours = [(9, 17), (10, 17)]

    # Define the days to consider
    days = ['Monday', 'Tuesday', 'Wednesday']

    # Iterate over each day
    for day in days:
        # Get Martha's schedule for the current day
        martha_day = martha_schedule.get(day, [])

        # Get Beverly's schedule for the current day
        beverly_day = beverly_schedule.get(day, [])

        # Iterate over each hour of the work day
        for start_hour, end_hour in work_hours:
            # Find a time slot that works for both Martha and Beverly
            for start_time in range(start_hour, end_hour):
                for end_time in range(start_time + 1, end_hour + 1):
                    # Check if the time slot works for Martha
                    martha_works = True
                    for time_range in martha_day:
                        if (start_time <= time_range[0] < end_time) or (start_time < time_range[1] <= end_time) or (time_range[0] <= start_time < time_range[1]) or (time_range[0] < end_time <= time_range[1]):
                            martha_works = False
                            break

                    # Check if the time slot works for Beverly
                    beverly_works = True
                    for time_range in beverly_day:
                        if (start_time <= time_range[0] < end_time) or (start_time < time_range[1] <= end_time) or (time_range[0] <= start_time < time_range[1]) or (time_range[0] < end_time <= time_range[1]):
                            beverly_works = False
                            break

                    # Check if the time slot is long enough for the meeting
                    if martha_works and beverly_works and end_time - start_time >= meeting_duration:
                        # Convert the time to a string
                        start_time_str = datetime.strptime(f"{day} {start_time}:00", "%A %H:%M").strftime("%H:%M")
                        end_time_str = datetime.strptime(f"{day} {end_time}:00", "%A %H:%M").strftime("%H:%M")

                        # Return the meeting time
                        return day, start_time_str, end_time_str

    # If no suitable time is found, return None
    return None


# Define the schedules
martha_schedule = {
    'Monday': [(9, 17), (16, 17)],
    'Tuesday': [(9, 17), (15, 15.5)],
    'Wednesday': [(9, 17), (10, 11), (14, 14.5)]
}

beverly_schedule = {
    'Monday': [(9, 13.5), (14, 17), (17, 17)],
    'Tuesday': [(9, 17)],
    'Wednesday': [(9, 15.5), (16, 17)]
}

# Define the meeting duration
meeting_duration = 60

# Find a suitable time for the meeting
meeting_time = find_meeting_time(martha_schedule, beverly_schedule, meeting_duration)

# Print the meeting time
if meeting_time:
    day, start_time, end_time = meeting_time
    print(f"{start_time}:{end_time} on {day}")
else:
    print("No suitable time found")