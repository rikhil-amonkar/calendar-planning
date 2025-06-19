from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    """
    Find the first available time slot in the given schedules.

    Args:
    start_time (datetime): The start time of the meeting.
    end_time (datetime): The end time of the meeting.
    schedules (dict): A dictionary of schedules where each key is a participant and each value is a list of tuples representing their busy times.

    Returns:
    tuple: The start and end times of the first available time slot.
    """
    # Initialize the current time to the start time
    current_time = start_time

    # Loop until we find an available time slot or reach the end time
    while current_time < end_time:
        # Check if the current time is available for all participants
        is_available = True
        for participant, busy_times in schedules.items():
            for busy_time in busy_times:
                # If the current time overlaps with a busy time, it's not available
                if busy_time[0] <= current_time < busy_time[1]:
                    is_available = False
                    break
            if not is_available:
                break

        # If the current time is available, return it
        if is_available:
            return current_time, current_time + timedelta(hours=0.5)

        # Otherwise, move to the next half hour
        current_time += timedelta(hours=0.5)

    # If we've reached the end time without finding an available time slot, return None
    return None


def schedule_meeting(start_time, end_time, schedules, preferences=None):
    """
    Schedule a meeting between the given participants.

    Args:
    start_time (datetime): The start of the workday.
    end_time (datetime): The end of the workday.
    schedules (dict): A dictionary of schedules where each key is a participant and each value is a list of tuples representing their busy times.
    preferences (dict): A dictionary of preferences where each key is a participant and each value is a list of preferred time slots.

    Returns:
    tuple: The start and end times of the scheduled meeting.
    """
    # Find the first available time slot
    available_time = find_available_time(start_time, end_time, schedules)

    # If no available time slot is found, return None
    if available_time is None:
        return None

    # If preferences are given, try to schedule the meeting at one of the preferred times
    if preferences:
        for participant, preferred_times in preferences.items():
            for preferred_time in preferred_times:
                # Check if the preferred time is available
                if find_available_time(preferred_time, preferred_time + timedelta(hours=0.5), schedules):
                    # If it's available, schedule the meeting at that time
                    return preferred_time, preferred_time + timedelta(hours=0.5)

    # If no preferred time is available, schedule the meeting at the first available time
    return available_time


def main():
    # Define the start and end times of the workday
    start_time = datetime(2024, 7, 29, 9, 0, 0)
    end_time = datetime(2024, 7, 29, 17, 0, 0)

    # Define the schedules of the participants
    schedules = {
        "Lisa": [(datetime(2024, 7, 29, 9, 0, 0), datetime(2024, 7, 29, 10, 0, 0)),
                 (datetime(2024, 7, 29, 10, 30, 0), datetime(2024, 7, 29, 11, 30, 0)),
                 (datetime(2024, 7, 29, 12, 30, 0), datetime(2024, 7, 29, 13, 0, 0)),
                 (datetime(2024, 7, 29, 16, 0, 0), datetime(2024, 7, 29, 16, 30, 0))],
        "Bobby": [(datetime(2024, 7, 29, 9, 0, 0), datetime(2024, 7, 29, 9, 30, 0)),
                  (datetime(2024, 7, 29, 10, 0, 0), datetime(2024, 7, 29, 10, 30, 0)),
                  (datetime(2024, 7, 29, 11, 30, 0), datetime(2024, 7, 29, 12, 0, 0)),
                  (datetime(2024, 7, 29, 15, 0, 0), datetime(2024, 7, 29, 15, 30, 0))],
        "Randy": [(datetime(2024, 7, 29, 9, 30, 0), datetime(2024, 7, 29, 10, 0, 0)),
                  (datetime(2024, 7, 29, 10, 30, 0), datetime(2024, 7, 29, 11, 0, 0)),
                  (datetime(2024, 7, 29, 11, 30, 0), datetime(2024, 7, 29, 12, 30, 0)),
                  (datetime(2024, 7, 29, 13, 0, 0), datetime(2024, 7, 29, 13, 30, 0)),
                  (datetime(2024, 7, 29, 14, 30, 0), datetime(2024, 7, 29, 15, 30, 0)),
                  (datetime(2024, 7, 29, 16, 0, 0), datetime(2024, 7, 29, 16, 30, 0))]
    }

    # Define the preferences of the participants
    preferences = {
        "Bobby": [(datetime(2024, 7, 29, 14, 30, 0), datetime(2024, 7, 29, 15, 0, 0))]
    }

    # Schedule the meeting
    meeting_time = schedule_meeting(start_time, end_time, schedules, preferences)

    # If a meeting time was found, print it
    if meeting_time:
        print(f"The meeting will be held on {start_time.strftime('%A')} from {meeting_time[0].strftime('%H:%M')} to {meeting_time[1].strftime('%H:%M')}.")
    else:
        print("No available time slot was found.")


if __name__ == "__main__":
    main()