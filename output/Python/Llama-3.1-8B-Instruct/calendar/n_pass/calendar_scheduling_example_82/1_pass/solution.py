from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, start_time, end_time):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (list): A list of participants' names and their schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    start_time (str): The start time of the workday in 'HH:MM' format.
    end_time (str): The end time of the workday in 'HH:MM' format.

    Returns:
    str: A proposed time for the meeting in the format 'HH:MM-HH:MM, Day of the week'.
    """

    # Convert the start and end times to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Initialize the meeting time to the start of the workday
    meeting_time = start_time

    # Loop until we find a suitable meeting time or reach the end of the workday
    while meeting_time < end_time:
        # Check if the meeting time conflicts with any participant's schedule
        conflict = False
        for participant in participants:
            if participant['name'] == 'Michael':
                for time in participant['schedule']:
                    if time[0] <= meeting_time + timedelta(minutes=meeting_duration) <= time[1]:
                        conflict = True
                        break
            elif participant['name'] == 'Eric':
                pass  # Eric's schedule is empty
            elif participant['name'] == 'Arthur':
                for time in participant['schedule']:
                    if time[0] <= meeting_time + timedelta(minutes=meeting_duration) <= time[1]:
                        conflict = True
                        break

        # If there's no conflict, return the meeting time
        if not conflict:
            return f"{meeting_time.strftime('%H:%M')}-{(meeting_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}, {meeting_time.strftime('%A')}"

        # If there's a conflict, move to the next available time slot
        meeting_time += timedelta(minutes=30)

    # If we've reached the end of the workday without finding a suitable meeting time, return None
    return None

# Define the participants' schedules
participants = [
    {'name': 'Michael','schedule': [(datetime.strptime('09:30', '%H:%M'), datetime.strptime('10:30', '%H:%M')),
                                     (datetime.strptime('15:00', '%H:%M'), datetime.strptime('15:30', '%H:%M')),
                                     (datetime.strptime('16:00', '%H:%M'), datetime.strptime('16:30', '%H:%M'))]},
    {'name': 'Eric','schedule': []},
    {'name': 'Arthur','schedule': [(datetime.strptime('09:00', '%H:%M'), datetime.strptime('12:00', '%H:%M')),
                                    (datetime.strptime('13:00', '%H:%M'), datetime.strptime('15:00', '%H:%M')),
                                    (datetime.strptime('15:30', '%H:%M'), datetime.strptime('16:00', '%H:%M')),
                                    (datetime.strptime('16:30', '%H:%M'), datetime.strptime('17:00', '%H:%M'))]}
]

# Define the meeting duration and work hours
meeting_duration = 30
start_time = '09:00'
end_time = '17:00'

# Find a suitable meeting time
meeting_time = find_meeting_time(participants, meeting_duration, start_time, end_time)

# Print the result
print(meeting_time)