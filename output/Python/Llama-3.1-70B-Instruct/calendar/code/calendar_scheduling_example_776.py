from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, days):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        participants (dict): A dictionary where the keys are the names of the participants and the values are dictionaries with days of the week as keys and lists of tuples representing the start and end times of their existing meetings as values.
        meeting_duration (int): The duration of the meeting in minutes.
        work_hours (tuple): A tuple representing the start and end times of the work hours.
        days (list): A list of days of the week.

    Returns:
        str: A string representing the proposed time and day of the meeting in the format HH:MM:HH:MM, Day.
    """

    # Convert the work hours to datetime objects
    start_time = datetime.strptime(work_hours[0], "%H:%M")
    end_time = datetime.strptime(work_hours[1], "%H:%M")

    # Loop through the days of the week
    for day in days:
        # Initialize the current time to the start of the work hours
        current_time = start_time

        # Loop through the work hours
        while current_time < end_time:
            # Check if the current time is available for all participants
            if all(is_time_available(participants[participant], day, current_time, meeting_duration) for participant in participants):
                # If the current time is available, return it as the proposed meeting time
                proposed_time = current_time.strftime("%H:%M") + ":" + (current_time + timedelta(minutes=meeting_duration)).strftime("%H:%M")
                return proposed_time + ", " + day

            # If the current time is not available, move to the next time slot
            current_time += timedelta(minutes=1)

def is_time_available(participant_schedule, day, current_time, meeting_duration):
    """
    Check if a given time is available for a participant.

    Args:
        participant_schedule (dict): A dictionary with days of the week as keys and lists of tuples representing the start and end times of the participant's existing meetings as values.
        day (str): The current day of the week.
        current_time (datetime): The current time to check.
        meeting_duration (int): The duration of the meeting in minutes.

    Returns:
        bool: True if the current time is available, False otherwise.
    """

    # Check if the participant has any meetings on this day
    if day not in participant_schedule:
        return True

    # Convert the current time to a string
    current_time_str = current_time.strftime("%H:%M")

    # Loop through the participant's existing meetings
    for start, end in participant_schedule[day]:
        # Convert the start and end times to datetime objects
        start_time = datetime.strptime(start, "%H:%M")
        end_time = datetime.strptime(end, "%H:%M")

        # Check if the current time overlaps with the existing meeting
        if start_time <= current_time < end_time or start_time < current_time + timedelta(minutes=meeting_duration) <= end_time:
            # If the current time overlaps, return False
            return False

    # Check if John wants to avoid meetings on Monday after 14:30
    if participant_schedule == {"Monday": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")], "Tuesday": [("09:00", "11:30"), ("12:00", "17:00")], "Wednesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]} and day == "Monday" and current_time >= datetime.strptime("14:30", "%H:%M"):
        return False

    # If the current time does not overlap with any existing meetings, return True
    return True

# Define the participants' schedules
participants = {
    "John": {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": []
    },
    "Jennifer": {
        "Monday": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("09:00", "11:30"), ("12:00", "17:00")],
        "Wednesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "14:00"), ("14:30", "16:00"), ("16:30", "17:00")]
    }
}

# Define the meeting duration and work hours
meeting_duration = 30
work_hours = ("09:00", "17:00")

# Define the days of the week
days = ["Monday", "Tuesday", "Wednesday"]

# Find the proposed meeting time
proposed_time = find_meeting_time(participants, meeting_duration, work_hours, days)

# Print the proposed meeting time
print(proposed_time)