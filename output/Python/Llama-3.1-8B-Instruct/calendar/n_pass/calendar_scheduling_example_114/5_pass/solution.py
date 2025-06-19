from datetime import datetime, timedelta

def find_available_time(start_time, end_time, schedules, duration=60):
    """
    Find the first available time slot in the given schedules.

    Args:
        start_time (datetime): The start time of the meeting.
        end_time (datetime): The end time of the meeting.
        schedules (dict): A dictionary of participants and their schedules.
        duration (int, optional): The duration of the meeting in minutes. Defaults to 60.

    Returns:
        tuple: The first available time slot or None if no slot is found.
    """
    available_time = None
    for minute in range((end_time - start_time).seconds // 60 + 1):
        time = start_time + timedelta(minutes=minute)
        if time + timedelta(minutes=duration) <= end_time:
            if all(not (start <= time < end and start < end <= time + timedelta(minutes=duration))
                   for schedule in schedules.values() for start, end in schedule):
                available_time = (time, time + timedelta(minutes=duration))
                break
        # If the time slot conflicts with an unavailable time slot, try the next minute
        continue
    return available_time


def schedule_meeting(start_time, end_time, schedules, preferences=None):
    """
    Schedule a meeting based on the given schedules and preferences.

    Args:
        start_time (datetime): The start time of the work hours.
        end_time (datetime): The end time of the work hours.
        schedules (dict): A dictionary of participants and their schedules.
        preferences (list, optional): A list of preferred time slots. Defaults to None.

    Returns:
        tuple: The scheduled time slot and the day of the week.
    """
    day_of_week = start_time.strftime('%A')
    available_time = find_available_time(start_time, end_time, schedules)
    if available_time:
        start, end = available_time
        return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}", day_of_week
    else:
        return "No available time slot found", day_of_week


# Example usage:
schedules = {
    'Stephanie': [(datetime(2024, 7, 22, 10), datetime(2024, 7, 22, 10, 30)),
                  (datetime(2024, 7, 22, 16), datetime(2024, 7, 22, 16, 30))],
    'Cheryl': [(datetime(2024, 7, 22, 10), datetime(2024, 7, 22, 10, 30)),
               (datetime(2024, 7, 22, 11, 30), datetime(2024, 7, 22, 12)),
               (datetime(2024, 7, 22, 13, 30), datetime(2024, 7, 22, 14)),
               (datetime(2024, 7, 22, 16, 30), datetime(2024, 7, 22, 17))],
    'Bradley': [(datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 10)),
                (datetime(2024, 7, 22, 10, 30), datetime(2024, 7, 22, 11, 30)),
                (datetime(2024, 7, 22, 13, 30), datetime(2024, 7, 22, 14)),
                (datetime(2024, 7, 22, 14, 30), datetime(2024, 7, 22, 15)),
                (datetime(2024, 7, 22, 15, 30), datetime(2024, 7, 22, 17))],
    'Steven': [(datetime(2024, 7, 22, 9), datetime(2024, 7, 22, 12)),
               (datetime(2024, 7, 22, 13), datetime(2024, 7, 22, 13, 30)),
               (datetime(2024, 7, 22, 14, 30), datetime(2024, 7, 22, 17)),
               (datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 10))],
}

start_time = datetime(2024, 7, 22, 9)
end_time = datetime(2024, 7, 22, 17)

scheduled_time, day_of_week = schedule_meeting(start_time, end_time, schedules)
print(f"Day of the week: {day_of_week}")
print(f"Scheduled time: {scheduled_time}")