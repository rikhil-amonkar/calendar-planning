from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules, preferences=None):
    """
    Find a suitable time for a meeting given the start and end times of the workday,
    the meeting duration, and the schedules of the participants.

    Args:
        start_time (datetime): The start time of the workday.
        end_time (datetime): The end time of the workday.
        duration (timedelta): The duration of the meeting.
        schedules (dict): A dictionary where the keys are the names of the participants
            and the values are lists of tuples representing their scheduled meetings.
        preferences (dict, optional): A dictionary where the keys are the names of the
            participants and the values are the preferred meeting times. Defaults to None.

    Returns:
        tuple: A tuple containing the start and end times of the proposed meeting.
    """
    # Initialize the proposed meeting time to the earliest possible time
    proposed_start_time = start_time
    proposed_end_time = proposed_start_time + duration

    # Loop until we find a suitable meeting time or we've tried all possible times
    while proposed_start_time < end_time:
        # Check if the proposed meeting time works for all participants
        works_for_all = True
        for participant, meetings in schedules.items():
            for meeting in meetings:
                # Check if the proposed meeting time overlaps with any of the participant's meetings
                if (proposed_start_time >= meeting[0] and proposed_start_time < meeting[1]) or \
                   (proposed_end_time > meeting[0] and proposed_end_time <= meeting[1]) or \
                   (proposed_start_time <= meeting[0] and proposed_end_time >= meeting[1]):
                    works_for_all = False
                    break
            if not works_for_all:
                break

        # If the proposed meeting time works for all participants, return it
        if works_for_all:
            return proposed_start_time.strftime("%H:%M"), proposed_end_time.strftime("%H:%M")

        # If the proposed meeting time doesn't work for all participants, try the next possible time
        proposed_start_time += timedelta(minutes=30)
        proposed_end_time = proposed_start_time + duration

    # If we've tried all possible times and haven't found a suitable meeting time, return None
    return None


def main():
    # Define the start and end times of the workday
    start_time = datetime(2024, 7, 22, 9, 0)
    end_time = datetime(2024, 7, 22, 17, 0)

    # Define the meeting duration
    duration = timedelta(hours=0, minutes=30)

    # Define the schedules of the participants
    schedules = {
        "Raymond": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 9, 30)),
                    (datetime(2024, 7, 22, 11, 30), datetime(2024, 7, 22, 12, 0)),
                    (datetime(2024, 7, 22, 13, 0), datetime(2024, 7, 22, 13, 30)),
                    (datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 15, 30))],
        "Billy": [(datetime(2024, 7, 22, 10, 0), datetime(2024, 7, 22, 10, 30)),
                  (datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 13, 0)),
                  (datetime(2024, 7, 22, 16, 30), datetime(2024, 7, 22, 17, 0))],
        "Donald": [(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 9, 30)),
                   (datetime(2024, 7, 22, 10, 0), datetime(2024, 7, 22, 11, 0)),
                   (datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 13, 0)),
                   (datetime(2024, 7, 22, 14, 0), datetime(2024, 7, 22, 14, 30)),
                   (datetime(2024, 7, 22, 16, 0), datetime(2024, 7, 22, 17, 0))]
    }

    # Define the preferred meeting times of the participants
    preferences = {
        "Billy": (datetime(2024, 7, 22, 14, 0), datetime(2024, 7, 22, 15, 0))
    }

    # Find a suitable meeting time
    proposed_start_time, proposed_end_time = find_meeting_time(start_time, end_time, duration, schedules, preferences)

    # Print the proposed meeting time and day of the week
    if proposed_start_time is not None:
        print(f"Monday, {proposed_start_time}:{proposed_end_time}")
    else:
        print("No suitable meeting time found")


if __name__ == "__main__":
    main()