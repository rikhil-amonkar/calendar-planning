from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, work_hours, days):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
    participants (dict): A dictionary where the keys are the names of the participants and the values are dictionaries with days of the week as keys and lists of tuples representing their busy times as values.
    meeting_duration (int): The duration of the meeting in minutes.
    work_hours (tuple): A tuple representing the start and end times of the workday.
    days (list): A list of days of the week.

    Returns:
    tuple: A tuple containing the proposed start time and end time of the meeting, and the day of the week.
    """

    # Convert work hours to datetime objects
    work_start = datetime.strptime(work_hours[0], "%H:%M")
    work_end = datetime.strptime(work_hours[1], "%H:%M")

    # Loop through the days
    for day in days:
        # Initialize the current time to the start of the workday
        current_time = work_start

        # Check if Stephanie wants to avoid this day
        if day == "Monday":
            continue

        # Check if Betty can meet on this day
        if day == "Tuesday":
            work_end = datetime.strptime("12:30", "%H:%M")

        # Loop through the workday
        while current_time < work_end:
            # Check if the current time is a valid meeting time for all participants
            valid_time = True
            for participant, schedule in participants.items():
                for busy_start, busy_end in schedule.get(day, []):
                    busy_start = datetime.strptime(busy_start, "%H:%M")
                    busy_end = datetime.strptime(busy_end, "%H:%M")
                    if current_time >= busy_start and current_time < busy_end:
                        valid_time = False
                        break
                if not valid_time:
                    break

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
    "Stephanie": {
        "Monday": [("09:30", "10:00"), ("10:30", "11:00"), ("11:30", "12:00"), ("14:00", "14:30")],
        "Tuesday": [("12:00", "13:00")],
        "Wednesday": [("09:00", "10:00"), ("13:00", "14:00")]
    },
    "Betty": {
        "Monday": [("09:00", "10:00"), ("11:00", "11:30"), ("14:30", "15:00"), ("15:30", "16:00")],
        "Tuesday": [("09:00", "09:30"), ("11:30", "12:00"), ("12:30", "14:30"), ("15:30", "16:00")],
        "Wednesday": [("10:00", "11:30"), ("12:00", "14:00"), ("14:30", "17:00")]
    }
}

# Define the meeting duration and work hours
meeting_duration = 60
work_hours = ("09:00", "17:00")
days = ["Monday", "Tuesday", "Wednesday"]

# Find a suitable time for the meeting
meeting_time = find_meeting_time(participants, meeting_duration, work_hours, days)

if meeting_time:
    print(f"Proposed meeting time: {meeting_time[0]}:{meeting_time[1]} on {meeting_time[2]}")
else:
    print("No suitable time found.")