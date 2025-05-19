from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, day):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary where the keys are the names of the participants and the values are lists of tuples representing their busy times.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the start and end times of the workday.
    day (str): The day of the week.

    Returns:
    tuple: A tuple containing the proposed start time and end time of the meeting, and the day of the week.
    """

    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_hours[0], "%H:%M")
    work_end = datetime.strptime(work_hours[1], "%H:%M")

    # Initialize the current time to the start of the workday
    current_time = work_start

    # Loop through the workday
    while current_time < work_end:
        # Check if the current time is a valid meeting time for all participants
        valid_time = True
        for participant, busy_times in participants.items():
            for busy_start, busy_end in busy_times:
                busy_start = datetime.strptime(busy_start, "%H:%M")
                busy_end = datetime.strptime(busy_end, "%H:%M")
                if current_time >= busy_start and current_time < busy_end:
                    valid_time = False
                    break
            if not valid_time:
                break

        # Check if Juan can meet at the current time
        if current_time.hour >= 16:
            valid_time = False

        # If the current time is valid, check if the meeting can be scheduled
        if valid_time:
            meeting_end = current_time + timedelta(minutes=meeting_duration)
            if meeting_end <= work_end:
                return (current_time.strftime("%H:%M"), meeting_end.strftime("%H:%M"), day)

        # Move to the next time slot
        current_time += timedelta(minutes=30)

    # If no valid time is found, return None
    return None


# Define the participants' schedules
participants = {
    "Juan": [("09:00", "10:30"), ("15:30", "16:00")],
    "Marilyn": [("11:00", "11:30"), ("12:30", "13:00")],
    "Ronald": [("09:00", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:00", "16:30")]
}

# Define the meeting duration and work hours
meeting_duration = 30
work_hours = ("09:00", "17:00")
day = "Monday"

# Find a suitable time for the meeting
meeting_time = find_meeting_time(participants, meeting_duration, work_hours, day)

if meeting_time:
    print(f"Proposed meeting time: {meeting_time[0]}:{meeting_time[1]} on {meeting_time[2]}")
else:
    print("No suitable time found.")