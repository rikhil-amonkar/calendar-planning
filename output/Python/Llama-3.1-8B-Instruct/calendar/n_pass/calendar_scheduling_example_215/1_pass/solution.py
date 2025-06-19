from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, participants):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (str): The start time of the day in 'HH:MM' format.
    end_time (str): The end time of the day in 'HH:MM' format.
    participants (dict): A dictionary where the keys are the participant names and the values are lists of their busy times.

    Returns:
    str: A proposed time in the format 'HH:MM-HH:MM' that works for everyone's schedule and constraints.
    """
    # Convert start and end times to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Initialize the current time to the start time
    current_time = start_time

    # Loop through the day in 30-minute increments
    while current_time < end_time:
        # Check if the current time works for all participants
        if all(not (start_time <= current_time < end_time) for start_time, end_time in participants[participant] for participant in participants):
            # If it does, return the current time as a string
            return f"{current_time.strftime('%H:%M')}-{(current_time + timedelta(minutes=30)).strftime('%H:%M')}"

        # If it doesn't, increment the current time by 30 minutes
        current_time += timedelta(minutes=30)

    # If no time is found, return an error message
    return "No time found that works for everyone's schedule and constraints."

# Define the participants and their busy times
participants = {
    'Steven': [],
    'Roy': [],
    'Cynthia': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
                (datetime.strptime('15:00', '%H:%M'), datetime.strptime('16:00', '%H:%M'))],
    'Lauren': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('09:30', '%H:%M')),
               (datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('13:00', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
               (datetime.strptime('14:00', '%H:%M'), datetime.strptime('14:30', '%H:%M')),
               (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
               (datetime.strptime('16:00', '%H:%M'), datetime.strptime('17:00', '%H:%M'))],
    'Robert': [(datetime.strptime('10:30', '%H:%M'), datetime.strptime('11:00', '%H:%M')),
               (datetime.strptime('11:30', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
               (datetime.strptime('12:30', '%H:%M'), datetime.strptime('13:30', '%H:%M')),
               (datetime.strptime('14:00', '%H:%M'), datetime.strptime('16:00', '%H:%M'))]
}

# Define the start and end times of the day
start_time = '09:00'
end_time = '17:00'

# Find a time that works for everyone's schedule and constraints
proposed_time = find_meeting_time(start_time, end_time, participants)

# Print the proposed time and the day of the week
print(f"Proposed time: {proposed_time}")
print(f"Day of the week: Monday")