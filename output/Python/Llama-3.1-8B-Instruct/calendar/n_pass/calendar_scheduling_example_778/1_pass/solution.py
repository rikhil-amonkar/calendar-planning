from datetime import datetime, timedelta

def find_meeting_time(susan_schedule, sandra_schedule, meeting_duration, day_preferences):
    """
    Find a suitable time for a meeting between Susan and Sandra.

    Args:
    - susan_schedule (dict): Susan's schedule with time slots as keys and boolean values indicating availability.
    - sandra_schedule (dict): Sandra's schedule with time slots as keys and boolean values indicating availability.
    - meeting_duration (int): The duration of the meeting in minutes.
    - day_preferences (list): A list of preferred days for the meeting.

    Returns:
    - A tuple containing the day of the week and the time range for the meeting.
    """

    # Define the start and end times for the work hours
    start_time = datetime.strptime('09:00', '%H:%M')
    end_time = datetime.strptime('17:00', '%H:%M')

    # Initialize the meeting time
    meeting_time = None

    # Iterate over the preferred days
    for day in day_preferences:
        # Determine the day of the week
        if day == 'Monday':
            day_name = 'Monday'
            day_start = datetime.strptime('09:00', '%H:%M')
            day_end = datetime.strptime('17:00', '%H:%M')
        elif day == 'Tuesday':
            day_name = 'Tuesday'
            day_start = datetime.strptime('09:00', '%H:%M')
            day_end = datetime.strptime('17:00', '%H:%M')
        elif day == 'Wednesday':
            day_name = 'Wednesday'
            day_start = datetime.strptime('09:00', '%H:%M')
            day_end = datetime.strptime('17:00', '%H:%M')

        # Generate time slots for the day
        time_slots = []
        current_time = day_start
        while current_time < day_end:
            time_slots.append((current_time.strftime('%H:%M'), (current_time + timedelta(minutes=30)).strftime('%H:%M')))
            current_time += timedelta(minutes=30)

        # Iterate over the time slots
        for slot in time_slots:
            # Check if the time slot is available for both Susan and Sandra
            if (slot[0] not in susan_schedule and slot[1] not in susan_schedule) and \
               (slot[0] not in sandra_schedule and slot[1] not in sandra_schedule):
                # Check if the time slot has enough duration for the meeting
                if (datetime.strptime(slot[1], '%H:%M') - datetime.strptime(slot[0], '%H:%M')).total_seconds() / 60 >= meeting_duration:
                    # Check if the time slot is not after 16:00 on Monday for Sandra
                    if day == 'Monday' and sandra_schedule.get('16:00', False):
                        continue
                    # Check if the time slot is not on Wednesday
                    if day == 'Wednesday':
                        continue
                    # Check if the time slot is not on Tuesday if Susan prefers not to meet on Tuesday
                    if day == 'Tuesday' and 'Tuesday' in day_preferences and day_preferences.index('Tuesday') > day_preferences.index(day):
                        continue
                    # Update the meeting time
                    meeting_time = (slot[0], slot[1], day_name)
                    break

        # If a meeting time is found, break the loop
        if meeting_time:
            break

    return meeting_time


# Define the schedules
susan_schedule = {
    'Monday': ['12:30', '13:00', '13:30', '14:00', 'Wednesday': ['9:30', '10:30', '14:00', '14:30', '15:30', '16:30']],
    'Tuesday': ['11:30', '12:00', 'Wednesday': ['9:30', '10:30', '14:00', '14:30', '15:30', '16:30']],
    'Wednesday': ['9:30', '10:30', '14:00', '14:30', '15:30', '16:30']
}

sandra_schedule = {
    'Monday': ['9:00', '13:00', '14:00', '15:00', '16:00', '16:30'],
    'Tuesday': ['9:00', '9:30', '10:30', '12:00', '12:30', '13:30', '14:00', '14:30', '16:00', '17:00'],
    'Wednesday': ['9:00', '11:30', '12:00', '12:30', '13:00', '17:00']
}

# Define the meeting duration
meeting_duration = 30

# Define the preferred days
day_preferences = ['Monday', 'Tuesday', 'Wednesday']

# Find a meeting time
meeting_time = find_meeting_time(susan_schedule, sandra_schedule, meeting_duration, day_preferences)

# Print the meeting time
if meeting_time:
    print(f"{meeting_time[2]}: {meeting_time[0]} - {meeting_time[1]}")
else:
    print("No meeting time found.")