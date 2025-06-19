from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedule, preferences):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (str): Start of the work hours in the format HH:MM.
    end_time (str): End of the work hours in the format HH:MM.
    meeting_duration (int): Duration of the meeting in minutes.
    schedule (dict): Dictionary of participants and their schedules.
    preferences (dict): Dictionary of participants and their preferences.

    Returns:
    str: Proposed time in the format HH:MM-HH:MM, day of the week.
    """
    # Convert time strings to datetime objects
    start_time = datetime.strptime(start_time, "%H:%M")
    end_time = datetime.strptime(end_time, "%H:%M")

    # Initialize proposed time
    proposed_time = None

    # Iterate over the work hours
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, 30):  # Check every 30 minutes
            # Create a datetime object for the current time
            time = datetime.combine(datetime.today(), datetime.min.time())
            time = time.replace(hour=hour, minute=minute)

            # Check if the time is available for all participants
            if all(time not in schedule[participant] for participant in schedule):
                # Check if the time meets the participant's preferences
                if all(time >= datetime.combine(datetime.today(), datetime.min.time()).replace(hour=preference['start'], minute=0) and time <= datetime.combine(datetime.today(), datetime.min.time()).replace(hour=preference['end'], minute=0) for participant, preference in preferences.items()):
                    # Check if the meeting can be scheduled at the current time
                    if time + timedelta(minutes=meeting_duration) <= end_time:
                        # Update the proposed time
                        proposed_time = time.strftime("%H:%M") + "-" + (time + timedelta(minutes=meeting_duration)).strftime("%H:%M")

    # Return the proposed time and the day of the week
    return f"{proposed_time}, {datetime.today().strftime('%A')}"

# Define the schedules and preferences
schedules = {
    'Judy': [],
    'Nicole': [
        (datetime.strptime('09:00', '%H:%M'), datetime.strptime('10:00', '%H:%M')),
        (datetime.strptime('10:30', '%H:%M'), datetime.strptime('16:30', '%H:%M'))
    ]
}

preferences = {
    'Nicole': {
       'start': 16,
        'end': 17
    }
}

# Find the meeting time
meeting_duration = 30
start_time = '09:00'
end_time = '17:00'

print(find_meeting_time(start_time, end_time, meeting_duration, schedules['Nicole'], preferences))