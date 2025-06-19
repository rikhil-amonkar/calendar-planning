from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, meeting_duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (datetime): The start time of the day.
        end_time (datetime): The end time of the day.
        meeting_duration (int): The duration of the meeting in minutes.
        schedules (dict): A dictionary of schedules where each key is a participant's name and each value is a list of tuples representing their busy times.

    Returns:
        tuple: A tuple containing the proposed time range and the day of the week.
    """
    # Generate all possible meeting times
    possible_times = []
    current_time = start_time
    while current_time < end_time:
        # Check if the current time is available for all participants
        is_available = True
        for participant, busy_times in schedules.items():
            for busy_time in busy_times:
                if current_time >= busy_time[0] and current_time < busy_time[1]:
                    is_available = False
                    break
            if not is_available:
                break
        # If the current time is available, add it to the list of possible times
        if is_available:
            possible_times.append((current_time, current_time + timedelta(minutes=meeting_duration)))
        current_time += timedelta(minutes=30)

    # Find the earliest available time
    if possible_times:
        proposed_time = min(possible_times, key=lambda x: x[0])
        return proposed_time, proposed_time[0].strftime("%A")
    else:
        return None, None

def main():
    # Define the schedules for each participant
    schedules = {
        "Denise": [(datetime(2024, 7, 29, 12, 0), datetime(2024, 7, 29, 12, 30)),
                   (datetime(2024, 7, 29, 15, 30), datetime(2024, 7, 29, 16, 0))],
        "Angela": [],
        "Natalie": [(datetime(2024, 7, 29, 9, 0), datetime(2024, 7, 29, 11, 30)),
                    (datetime(2024, 7, 29, 12, 0), datetime(2024, 7, 29, 13, 0)),
                    (datetime(2024, 7, 29, 14, 0), datetime(2024, 7, 29, 14, 30)),
                    (datetime(2024, 7, 29, 15, 0), datetime(2024, 7, 29, 17, 0))]
    }

    # Define the meeting duration and the day of the week
    meeting_duration = 30  # minutes
    start_time = datetime(2024, 7, 29, 9, 0)
    end_time = datetime(2024, 7, 29, 17, 0)

    # Find a time that works for everyone's schedule and constraints
    proposed_time, day_of_week = find_meeting_time(start_time, end_time, meeting_duration, schedules)

    # Output the proposed time and the day of the week
    if proposed_time:
        print(f"{proposed_time[0].strftime('%H:%M')} - {proposed_time[1].strftime('%H:%M')}: {day_of_week}")
    else:
        print("No available time found.")

if __name__ == "__main__":
    main()