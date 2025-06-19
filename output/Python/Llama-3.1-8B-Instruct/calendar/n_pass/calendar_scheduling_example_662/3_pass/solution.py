from datetime import datetime, timedelta

def find_meeting_time(gary_schedule, david_schedule, meeting_duration):
    """
    Find a time that works for both Gary and David's schedules.

    Args:
        gary_schedule (dict): Gary's schedule with start and end times for each day.
        david_schedule (dict): David's schedule with start and end times for each day.
        meeting_duration (int): The duration of the meeting in minutes.

    Returns:
        tuple: A proposed time and day for the meeting in the format HH:MM-HH:MM, Day.
    """

    # Define the work hours and days
    work_hours = [(9, 17)]
    work_days = ['Monday', 'Tuesday']

    # Iterate over each day
    for day in work_days:
        # Initialize the start time to 9:00
        start_time = 9 * 60

        # Iterate over each hour
        while start_time < 17 * 60:
            # Check if the time slot is available for both Gary and David
            if (start_time + meeting_duration) not in gary_schedule.get(day, []) and \
               (start_time + meeting_duration) not in david_schedule.get(day, []):
                # Check if the time slot conflicts with an unavailable time slot
                conflict = False
                for unavailable_start in gary_schedule.get(day, []):
                    if start_time <= unavailable_start < start_time + meeting_duration:
                        conflict = True
                        break
                for unavailable_start in david_schedule.get(day, []):
                    if start_time <= unavailable_start < start_time + meeting_duration:
                        conflict = True
                        break

                # Check for time slot conflicts from 9.5 to 10
                if start_time + 30 >= 540 and start_time + 30 <= 600:
                    conflict = True

                if conflict:
                    start_time += 30
                    continue

                # Return the proposed time and day
                end_time = start_time + meeting_duration
                return f"{start_time // 60:02d}:{start_time % 60:02d}-{end_time // 60:02d}:{end_time % 60:02d}", day

            # Move to the next time slot
            start_time += 30

    # If no time slot is available, return None
    return None


# Define Gary's schedule
gary_schedule = {
    'Monday': [90, 390, 780, 1170],
    'Tuesday': [30, 90, 780, 1140]
}

# Define David's schedule
david_schedule = {
    'Monday': [30, 90, 390, 1170],
    'Tuesday': [30, 90, 150, 390, 630, 780, 1140, 1500, 1170]
}

# Define the meeting duration
meeting_duration = 60

# Find a time that works for both Gary and David's schedules
proposed_time, day = find_meeting_time(gary_schedule, david_schedule, meeting_duration)

# Print the proposed time and day
if proposed_time:
    print(f"Proposed time: {proposed_time}, Day: {day}")
else:
    print("No time slot available.")