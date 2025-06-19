from datetime import datetime, timedelta

def schedule_meeting(participants, start_time, end_time, duration, preferences=None):
    """
    Schedules a meeting between participants based on their busy time slots and preferences.

    Args:
        participants (dict): A dictionary of participants where each participant is a dictionary with 'busy' and 'preference' keys.
        start_time (datetime): The start time of the workday.
        end_time (datetime): The end time of the workday.
        duration (timedelta): The duration of the meeting.
        preferences (dict, optional): A dictionary of preferences where each preference is a dictionary with'start' and 'end' keys. Defaults to None.

    Returns:
        str: The scheduled meeting time or None if no meeting time is found.
    """

    # Initialize the meeting time
    meeting_time = start_time

    while meeting_time < end_time:
        # Check if the meeting time is within the workday hours
        if meeting_time + duration > end_time:
            break

        # Check if all participants are available at the meeting time
        if all(
            not (meeting_time + duration).time() < participant['busy'][i]['end'].time() and
            not (meeting_time - duration).time() > participant['busy'][i]['start'].time() and
            (meeting_time + duration).time() >= participant['busy'][i]['start'].time() and
            (meeting_time - duration).time() <= participant['busy'][i]['end'].time()
            for participant in participants.values() for i in range(len(participant['busy']))
        ):
            # Check if the meeting time meets any participant's preference
            if all(
                not (meeting_time + duration).time() < participant['preference']['end'].time() and
                not (meeting_time - duration).time() > participant['preference']['start'].time()
                for participant in participants.values()
            ):
                # Return the meeting time if it meets all conditions
                return f"{meeting_time.strftime('%H:%M')} - {(meeting_time + duration).strftime('%H:%M')} on {start_time.strftime('%A')}"

        # Move to the next available time slot
        meeting_time += timedelta(minutes=30)

    # Return None if no meeting time is found
    return None

# Define the participants' schedules
participants = {
    'Natalie': {'busy': [], 'preference': {'start': datetime(2024, 7, 22, 10, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
    'David': {'busy': [{'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 0)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}], 'preference': {'start': datetime(2024, 7, 22, 14, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
    'Douglas': {'busy': [{'start': datetime(2024, 7, 22, 9, 30), 'end': datetime(2024, 7, 22, 10, 0)}, {'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 0)}, {'start': datetime(2024, 7, 22, 13, 0), 'end': datetime(2024, 7, 22, 13, 30)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}], 'preference': {'start': datetime(2024, 7, 22, 14, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
    'Ralph': {'busy': [{'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 9, 30)}, {'start': datetime(2024, 7, 22, 10, 0), 'end': datetime(2024, 7, 22, 11, 0)}, {'start': datetime(2024, 7, 22, 11, 30), 'end': datetime(2024, 7, 22, 12, 30)}, {'start': datetime(2024, 7, 22, 13, 30), 'end': datetime(2024, 7, 22, 15, 0)}, {'start': datetime(2024, 7, 22, 15, 30), 'end': datetime(2024, 7, 22, 16, 0)}, {'start': datetime(2024, 7, 22, 16, 30), 'end': datetime(2024, 7, 22, 17, 0)}], 'preference': {'start': datetime(2024, 7, 22, 14, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
    'Jordan': {'busy': [{'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 10, 0)}, {'start': datetime(2024, 7, 22, 12, 0), 'end': datetime(2024, 7, 22, 12, 30)}, {'start': datetime(2024, 7, 22, 13, 0), 'end': datetime(2024, 7, 22, 13, 30)}, {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)}, {'start': datetime(2024, 7, 22, 15, 30), 'end': datetime(2024, 7, 22, 17, 0)}], 'preference': {'start': datetime(2024, 7, 22, 14, 0), 'end': datetime(2024, 7, 22, 17, 0)}},
}

# Define the start and end time of the workday
start_time = datetime(2024, 7, 22, 9, 0)
end_time = datetime(2024, 7, 22, 17, 0)

# Define the meeting duration
duration = timedelta(minutes=30)

# Find a suitable meeting time
meeting_time = schedule_meeting(participants, start_time, end_time, duration)

# Print the result
if meeting_time:
    print(meeting_time)
else:
    print("No meeting time found.")