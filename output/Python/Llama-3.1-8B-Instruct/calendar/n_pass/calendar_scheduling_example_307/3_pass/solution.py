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

    for start_hour in range(9, 17):
        for end_hour in range(start_hour + 1, 17):
            meeting_start = datetime.strptime(f"{start_hour}:00", "%H:%M")
            meeting_end = datetime.strptime(f"{end_hour}:00", "%H:%M") + timedelta(minutes=meeting_duration)

            # Check if meeting fits within work hours
            if meeting_start < datetime.strptime("17:00", "%H:%M") and meeting_end > datetime.strptime("9:00", "%H:%M"):
                # Check if meeting conflicts with any participant's schedule
                if all(
                    not (
                        meeting_start.time() < start < meeting_end.time()
                        or meeting_start.time() < end < meeting_end.time()
                        or start <= meeting_start.time() < end
                        or start < meeting_end.time() <= end
                    )
                    for name, schedule in participants_list
                    for start, end in schedule
                ):
                    return f"{meeting_start.strftime('%H:%M')} - {meeting_end.strftime('%H:%M')} - {meeting_end.strftime('%A')}"

    return "No meeting time found"

# Define participants' schedules
participants = {
    "Ronald": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Stephen": [(datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")), (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M"))],
    "Brittany": [(datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")), (datetime.strptime("13:30", "%H:%M"), datetime.strptime("14:00", "%H:%M")), (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M")), (datetime.strptime("16:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Dorothy": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")), (datetime.strptime("10:00", "%H:%M"), datetime.strptime("10:30", "%H:%M")), (datetime.strptime("11:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")), (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")), (datetime.strptime("15:30", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Rebecca": [(datetime.strptime("9:30", "%H:%M"), datetime.strptime("10:30", "%H:%M")), (datetime.strptime("11:00", "%H:%M"), datetime.strptime("11:30", "%H:%M")), (datetime.strptime("12:00", "%H:%M"), datetime.strptime("12:30", "%H:%M")), (datetime.strptime("13:00", "%H:%M"), datetime.strptime("17:00", "%H:%M"))],
    "Jordan": [(datetime.strptime("9:00", "%H:%M"), datetime.strptime("9:30", "%H:%M")), (datetime.strptime("10:00", "%H:%M"), datetime.strptime("11:00", "%H:%M")), (datetime.strptime("11:30", "%H:%M"), datetime.strptime("12:00", "%H:%M")), (datetime.strptime("13:00", "%H:%M"), datetime.strptime("15:00", "%H:%M")), (datetime.strptime("15:30", "%H:%M"), datetime.strptime("16:00", "%H:%M"))],
}

# Define meeting duration in minutes
meeting_duration = 30

# Find meeting time
meeting_time = find_meeting_time(participants, meeting_duration)

# Print meeting time
print(meeting_time)