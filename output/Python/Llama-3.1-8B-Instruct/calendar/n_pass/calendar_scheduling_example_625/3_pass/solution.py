from datetime import datetime, timedelta

def find_meeting_time(jeffrey_free_time, harold_schedule, meeting_duration, day):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    - jeffrey_free_time (list): List of tuples representing Jeffrey's free time.
    - harold_schedule (dict): Dictionary representing Harold's schedule.
    - meeting_duration (int): Duration of the meeting in minutes.
    - day (str): Day of the week.

    Returns:
    - proposed_time (str): Proposed time for the meeting in the format HH:MM-HH:MM.
    - day (str): Day of the week.
    """
    # Filter Harold's schedule for the given day
    harold_schedule_day = {time: duration for time, duration in harold_schedule.items() if time[0] == day}

    # Iterate over Jeffrey's free time
    for jeffrey_time in jeffrey_free_time:
        # Iterate over Harold's schedule for the given day
        for harold_time, duration in harold_schedule_day.items():
            # Convert the time to datetime objects for easier comparison
            jeffrey_time_start = datetime.strptime(jeffrey_time[0], '%H:%M')
            jeffrey_time_end = datetime.strptime(jeffrey_time[1], '%H:%M')
            harold_time_start = datetime.strptime(harold_time[0], '%H:%M')
            harold_time_end = datetime.strptime(harold_time[1], '%H:%M')

            # Check if the meeting time fits within Harold's free time
            if (harold_time_start <= jeffrey_time_start <= harold_time_end) and (harold_time_start + timedelta(minutes=duration) <= jeffrey_time_start + timedelta(minutes=meeting_duration)):
                # Check if Harold prefers to avoid more meetings on Monday or Tuesday before 14:30
                if (day == 'Monday' and jeffrey_time_start < datetime.strptime('14:30', '%H:%M')) or (day == 'Tuesday' and jeffrey_time_start < datetime.strptime('14:30', '%H:%M')):
                    continue
                # Check if the meeting time fits within Jeffrey's free time
                if jeffrey_time_start + timedelta(minutes=meeting_duration) <= jeffrey_time_end:
                    # Calculate the end time of the meeting
                    end_time = jeffrey_time_start + timedelta(minutes=meeting_duration)
                    # Format the proposed time
                    proposed_time = f"{jeffrey_time_start.strftime('%H:%M')}-{end_time.strftime('%H:%M')}"
                    return proposed_time, day

    # If no suitable time is found, return None
    return None, None


# Define the existing schedules for everyone during the days
jeffrey_free_time = [(9, 17), (10, 17), (11, 17), (12, 17), (13, 17), (14, 17), (15, 17), (16, 17)]
harold_schedule = {
    'Monday': [(9, '10'), ('10:30', 7), (12, 1), (14, 1), (16, 1)],
    'Tuesday': [('9', '9:30'), ('10:30', 1.5), ('12:30', 1.5), ('14:30', 1.5), (16, 1)]
}
meeting_duration = 30
day = 'Monday'

# Find a suitable time for the meeting
proposed_time, day = find_meeting_time(jeffrey_free_time, harold_schedule, meeting_duration, day)

# Print the proposed time and day
if proposed_time:
    print(f"Proposed time: {proposed_time} on {day}")
else:
    print("No suitable time found.")