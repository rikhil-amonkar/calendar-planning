from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules):
    """
    Find the first available time slot in the given schedules.

    Args:
    start_time (tuple): The start time of the meeting as a tuple of (year, month, day, hour, minute, second).
    end_time (tuple): The end time of the meeting as a tuple of (year, month, day, hour, minute, second).
    schedules (dict): A dictionary of schedules where each key is a participant and each value is a list of tuples representing their busy times.

    Returns:
    tuple: The start and end times of the first available time slot.
    """
    # Initialize the current time to the start time
    current_time = datetime(*start_time)

    # Loop until we find an available time slot or reach the end time
    while current_time < datetime(*end_time):
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
            return (current_time.year, current_time.month, current_time.day, current_time.hour, current_time.minute, current_time.second), \
                   (current_time.year, current_time.month, current_time.day, (current_time + timedelta(hours=1)).hour, current_time.minute, current_time.second)

        # Otherwise, move to the next hour
        current_time += timedelta(hours=1)

    # If we've reached the end time without finding an available time slot, return None
    return None


def schedule_meeting(start_time, end_time, schedules, preferences=None):
    """
    Schedule a meeting between the given participants.

    Args:
    start_time (tuple): The start of the workday as a tuple of (year, month, day, hour, minute, second).
    end_time (tuple): The end of the workday as a tuple of (year, month, day, hour, minute, second).
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
                preferred_time = datetime(*preferred_time)
                if find_available_time((preferred_time.year, preferred_time.month, preferred_time.day, preferred_time.hour, preferred_time.minute, 0), (preferred_time.year, preferred_time.month, preferred_time.day, (preferred_time + timedelta(hours=1)).hour, preferred_time.minute, 0), schedules):
                    # If it's available, schedule the meeting at that time
                    return (preferred_time.year, preferred_time.month, preferred_time.day, preferred_time.hour, preferred_time.minute, 0), \
                           (preferred_time.year, preferred_time.month, preferred_time.day, (preferred_time + timedelta(hours=1)).hour, preferred_time.minute, 0)

    # If no preferred time is available, schedule the meeting at the first available time
    return available_time


def main():
    # Define the start and end times of the workday
    start_time = (2024, 7, 29, 9, 0, 0)
    end_time = (2024, 7, 29, 17, 0, 0)

    # Define the schedules of the participants
    schedules = {
        "Lisa": [(2024, 7, 29, 9, 0, 0), (2024, 7, 29, 10, 0, 0),
                 (2024, 7, 29, 10, 30, 0), (2024, 7, 29, 11, 30, 0),
                 (2024, 7, 29, 12, 30, 0), (2024, 7, 29, 13, 0, 0),
                 (2024, 7, 29, 16, 0, 0), (2024, 7, 29, 16, 30, 0)],
        "Bobby": [(2024, 7, 29, 9, 0, 0), (2024, 7, 29, 9, 30, 0),
                  (2024, 7, 29, 10, 0, 0), (2024, 7, 29, 10, 30, 0),
                  (2024, 7, 29, 11, 30, 0), (2024, 7, 29, 12, 0, 0),
                  (2024, 7, 29, 15, 0, 0), (2024, 7, 29, 15, 30, 0)],
        "Randy": [(2024, 7, 29, 9, 30, 0), (2024, 7, 29, 10, 0, 0),
                  (2024, 7, 29, 10, 30, 0), (2024, 7, 29, 11, 0, 0),
                  (2024, 7, 29, 11, 30, 0), (2024, 7, 29, 12, 30, 0),
                  (2024, 7, 29, 13, 0, 0), (2024, 7, 29, 13, 30, 0),
                  (2024, 7, 29, 14, 30, 0), (2024, 7, 29, 15, 30, 0),
                  (2024, 7, 29, 16, 0, 0), (2024, 7, 29, 16, 30, 0)]
    }

    # Define the preferences of the participants
    preferences = {
        "Bobby": [(2024, 7, 29, 14, 30, 0), (2024, 7, 29, 15, 0, 0)]
    }

    # Schedule the meeting
    meeting_time = schedule_meeting(start_time, end_time, schedules, preferences)

    # If a meeting time was found, print it
    if meeting_time:
        print(f"The meeting will be held on {datetime(*start_time).strftime('%A')} from {datetime(*meeting_time[0]).strftime('%H:%M')} to {datetime(*meeting_time[1]).strftime('%H:%M')}.")
    else:
        print("No available time slot was found.")


if __name__ == "__main__":
    main()