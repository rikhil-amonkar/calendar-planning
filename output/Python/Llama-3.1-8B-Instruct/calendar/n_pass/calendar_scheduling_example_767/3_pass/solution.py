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
            for start_time in range(start_hour * 60, end_hour * 60):
                # Check if the time slot works for Martha
                martha_works = True
                for time_range in martha_day:
                    if (start_time <= time_range[0] < start_time + meeting_duration) or (start_time < time_range[1] <= start_time + meeting_duration) or (time_range[0] <= start_time < time_range[1]) or (time_range[0] < start_time + meeting_duration <= time_range[1]):
                        martha_works = False
                        break

                # Check if the time slot works for Beverly
                beverly_works = True
                for time_range in beverly_day:
                    if (start_time <= time_range[0] < start_time + meeting_duration) or (start_time < time_range[1] <= start_time + meeting_duration) or (time_range[0] <= start_time < time_range[1]) or (time_range[0] < start_time + meeting_duration <= time_range[1]):
                        beverly_works = False
                        break

                # Check if the time slot is long enough for the meeting
                if martha_works and beverly_works and start_time + meeting_duration <= end_hour * 60:
                    # Convert the time to a string
                    start_time_str = datetime.strptime(f"{day} {start_time // 60}:{start_time % 60:02d}", "%A %H:%M").strftime("%H:%M")
                    end_time_str = datetime.strptime(f"{day} {(start_time // 60) + (meeting_duration // 60)}:{(start_time % 60) + (meeting_duration % 60):02d}", "%A %H:%M").strftime("%H:%M")

                    # Return the meeting time
                    return day, start_time_str, end_time_str

    # If no suitable time is found, return None
    return None


# Define the schedules
martha_schedule = {
    'Monday': [(9 * 60, 17 * 60), (16 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 17 * 60), (15 * 60, 15.5 * 60)],
    'Wednesday': [(9 * 60, 17 * 60), (10 * 60, 11 * 60), (14 * 60, 14.5 * 60)]
}

beverly_schedule = {
    'Monday': [(9 * 60, 13.5 * 60), (14 * 60, 17 * 60), (17 * 60, 17 * 60)],
    'Tuesday': [(9 * 60, 17 * 60)],
    'Wednesday': [(9 * 60, 15.5 * 60), (16 * 60, 17 * 60)]
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