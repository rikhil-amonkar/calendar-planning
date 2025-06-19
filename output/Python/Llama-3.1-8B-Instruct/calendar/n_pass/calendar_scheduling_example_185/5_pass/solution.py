from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, participants, meeting_duration):
    """
    Find a time that works for all participants.

    Args:
    start_time (str): The start time of the workday in HH:MM format.
    end_time (str): The end time of the workday in HH:MM format.
    participants (dict): A dictionary where the keys are participant names and the values are lists of their busy times.
    meeting_duration (int): The duration of the meeting in minutes.

    Returns:
    str: A string representing the proposed time in the format HH:MM-HH:MM, Day of the week.
    """

    # Convert the start and end times to datetime objects
    start_time = datetime.strptime(start_time, '%H:%M')
    end_time = datetime.strptime(end_time, '%H:%M')

    # Convert the busy times to datetime objects
    for participant in participants.values():
        for i in range(len(participant)):
            participant[i] = datetime.strptime(participant[i], '%H:%M')

    # Initialize the meeting time to the start of the workday
    meeting_time = start_time

    # Loop until we find a time that works for all participants
    while meeting_time < end_time:
        # Check if the meeting time works for all participants
        works_for_all = True
        for participant, busy_times in participants.items():
            for busy_time in busy_times:
                # Check if the meeting time conflicts with the busy time
                if meeting_time < busy_time and (meeting_time + timedelta(minutes=meeting_duration)).replace(minute=0, second=0) > busy_time:
                    works_for_all = False
                    break
            if not works_for_all:
                break

        # Check if the meeting time conflicts with the unavailable time slot on Monday from 0 to 12
        if meeting_time.strftime('%A') == 'Monday' and (0 <= meeting_time.hour < 12):
            works_for_all = False

        # If the meeting time works for all participants, return it
        if works_for_all:
            return f"{meeting_time.strftime('%H:%M')} - {(meeting_time + timedelta(minutes=meeting_duration)).strftime('%H:%M')}, {meeting_time.strftime('%A')}"

        # If the meeting time does not work for all participants, move to the next time
        meeting_time += timedelta(minutes=1)

    # If we have looped through the entire workday and not found a time that works for all participants, return a message
    return "No time found that works for all participants."


# Define the participants and their busy times
participants = {
    'Kimberly': ['10:00', '11:00', '16:00'],
    'Megan': [],
    'Marie': ['10:00', '11:30', '16:00'],
    'Diana': ['09:00', '10:30', '15:30']
}

# Define the start and end times of the workday
start_time = '09:00'
end_time = '17:00'

# Define the meeting duration
meeting_duration = 30

# Find a time that works for all participants
print(find_meeting_time(start_time, end_time, participants, meeting_duration))