from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration):
    """
    Find a meeting time that fits within work hours and does not conflict with any participant's schedule.

    Args:
        participants (dict): A dictionary where the keys are participant names and the values are their schedules.
        meeting_duration (int): The duration of the meeting in minutes.

    Returns:
        str: A string representing the meeting time in the format "HH:MM - Day of the Week" if a meeting time is found, otherwise "No meeting time found".
    """

    # Convert the participants dictionary to a list of tuples
    participants_list = [(name, schedule) for name, schedule in participants.items()]

    # Sort the participants by their earliest end time
    participants_list.sort(key=lambda x: min(end for start, end in x[1]))

    for start_time in range(9, 17):
        for end_time in range(start_time + 1, 17):
            meeting_start = datetime.strptime(f"{start_time}:00", "%H:%M")
            meeting_end = datetime.strptime(f"{end_time}:00", "%H:%M") + timedelta(minutes=meeting_duration)

            # Check if meeting fits within work hours
            if meeting_start < datetime.strptime("17:00", "%H:%M") and meeting_end > datetime.strptime("9:00", "%H:%M"):
                # Check if meeting conflicts with any participant's schedule
                if all(
                    not (
                        start_time <= start.hour < end_time
                        or start_time < end.hour < end_time
                        or start.hour <= start_time < end.hour
                        or start.hour < end_time <= end.hour
                    )
                    for name, schedule in participants_list
                    for start, end in schedule
                ):
                    return f"{meeting_start.strftime('%H:%M')}:{meeting_end.strftime('%H:%M')} - {meeting_end.strftime('%A')}"

    return "No meeting time found"

# Define participants' schedules
participants = {
    "Ronald": [(9, 17)],
    "Stephen": [(10, 10.5), (12, 12.5)],
    "Brittany": [(11, 11.5), (13.5, 14), (15.5, 16), (16.5, 17)],
    "Dorothy": [(9, 9.5), (10, 10.5), (11, 12.5), (13, 15), (15.5, 17)],
    "Rebecca": [(9.5, 10.5), (11, 11.5), (12, 12.5), (13, 17)],
    "Jordan": [(9, 9.5), (10, 11), (11.5, 12), (13, 15), (15.5, 16.5)],
}

# Define meeting duration in minutes
meeting_duration = 30

# Find meeting time
meeting_time = find_meeting_time(participants, meeting_duration)

# Print meeting time
print(meeting_time)