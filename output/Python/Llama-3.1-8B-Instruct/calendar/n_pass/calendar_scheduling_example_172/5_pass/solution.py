from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    """
    Find the earliest available time slot for a meeting with the given participants and meeting duration.

    Args:
    participants (list): A list of dictionaries containing the participants' busy times.
    meeting_duration (int): The duration of the meeting in minutes.

    Returns:
    str: The earliest available time slot in the format 'HH:MM-HH:MM on Day'.
    """
    # Define the start and end of the work hours
    start_time = datetime.strptime('09:00', '%H:%M').time()
    end_time = datetime.strptime('17:00', '%H:%M').time()

    # Convert the busy times to datetime objects
    busy_times = {}
    for participant in participants:
        for busy_time in participant['busy']:
            start, end = busy_time.split('-')
            start_time_obj = datetime.strptime(start, '%H:%M').time()
            end_time_obj = datetime.strptime(end, '%H:%M').time()
            busy_times[start_time_obj] = end_time_obj

    # Find the earliest available time slot for all participants
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, meeting_duration):
            # Create a datetime object for the current time
            time = datetime.combine(datetime.today().date(), datetime.time(hour, minute))

            # Calculate the end time of the meeting
            time_end = time + timedelta(minutes=meeting_duration)

            # Check if the time slot is available for all participants
            if all(not (time < datetime.combine(datetime.today().date(), busy_time) and datetime.combine(datetime.today().date(), busy_time) < time_end) 
                   for busy_time in busy_times.values()):
                return f"{time.strftime('%H:%M')}-{(time_end).strftime('%H:%M')} on {datetime.today().strftime('%A')}"

    return "No available time slot found"

# Define the participants' schedules
participants = [
    {'name': 'Patrick', 'busy': ['09:00-09:30', '10:00-10:30', '13:30-14:00', '16:00-16:30']},
    {'name': 'Kayla', 'busy': ['12:30-13:30', '15:00-15:30', '16:00-16:30']},
    {'name': 'Carl', 'busy': ['10:30-11:00', '12:00-12:30', '13:00-13:30', '14:30-17:00']},
    {'name': 'Christian', 'busy': ['09:00-12:30', '13:00-14:00', '14:30-17:00']}
]

# Find the meeting time
meeting_duration = 30  # in minutes
print(find_meeting_time(participants, meeting_duration))