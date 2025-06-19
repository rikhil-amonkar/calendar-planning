from datetime import datetime, timedelta

def find_meeting_time(participants, meeting_duration, max_end_time):
    """
    Find a time slot that works for all participants.

    Args:
    participants (dict): A dictionary where keys are participant names and values are their schedules.
    meeting_duration (int): The duration of the meeting in minutes.
    max_end_time (int): The latest end time of the meeting in minutes.

    Returns:
    tuple: A tuple containing the start and end times of the meeting in minutes.
    """
    # Sort the participants by their earliest available time
    sorted_participants = sorted(participants.items(), key=lambda x: min([t for t in x[1] if t < max_end_time]))

    # Initialize the earliest available time for the first participant
    earliest_start_time = min([t for t in sorted_participants[0][1] if t < max_end_time])

    # Initialize the end time of the meeting
    end_time = earliest_start_time + timedelta(minutes=meeting_duration)

    # Check if the end time is within the allowed range
    if end_time > max_end_time:
        return None

    # Check if all participants are available during the meeting time
    for participant, schedule in participants.items():
        # Find the overlap between the meeting time and the participant's schedule
        overlap = [t for t in schedule if t < end_time and t > earliest_start_time]

        # If there is no overlap, return None
        if not overlap:
            return None

    # If all participants are available, return the meeting time
    return (earliest_start_time.timestamp(), end_time.timestamp())


def get_day_of_week(day):
    """
    Get the day of the week given the day of the month.

    Args:
    day (int): The day of the month.

    Returns:
    str: The day of the week.
    """
    days_of_week = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday", "Sunday"]
    return days_of_week[(datetime.now().weekday() + (day - 1)) % 7]


def main():
    # Define the schedules for each participant
    anthony_schedule = [
        datetime(2024, 7, 22, 9, 30),
        datetime(2024, 7, 22, 12, 0),
        datetime(2024, 7, 22, 16, 0),
        datetime(2024, 7, 22, 16, 30)
    ]
    pamela_schedule = [
        datetime(2024, 7, 22, 9, 30),
        datetime(2024, 7, 22, 16, 30),
        datetime(2024, 7, 22, 17, 0)
    ]
    zachary_schedule = [
        datetime(2024, 7, 22, 9, 0),
        datetime(2024, 7, 22, 11, 30),
        datetime(2024, 7, 22, 12, 0),
        datetime(2024, 7, 22, 13, 0),
        datetime(2024, 7, 22, 14, 30),
        datetime(2024, 7, 22, 15, 0),
        datetime(2024, 7, 22, 16, 0),
        datetime(2024, 7, 22, 17, 0)
    ]

    # Define the meeting duration and the maximum end time
    meeting_duration = 60
    max_end_time = 17 * 60

    # Define the day of the week
    day_of_week = get_day_of_week(22)

    # Find the meeting time
    meeting_time = find_meeting_time({
        "Anthony": anthony_schedule,
        "Pamela": pamela_schedule,
        "Zachary": zachary_schedule
    }, meeting_duration, max_end_time)

    # If a meeting time is found, print it
    if meeting_time:
        start_time = datetime.fromtimestamp(meeting_time[0])
        end_time = datetime.fromtimestamp(meeting_time[1])
        print(f"{day_of_week}: {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}")
    else:
        print("No meeting time found")


if __name__ == "__main__":
    main()