from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, day, schedules):
    """
    Find available time slots on the given day.

    Args:
        start_time (int): The start time of the day in 30-minute increments.
        end_time (int): The end time of the day in 30-minute increments.
        duration (int): The duration of the meeting in minutes.
        day (str): The day of the week.
        schedules (dict): A dictionary of schedules for each day.

    Returns:
        tuple or None: A tuple containing the start and end times of the meeting, or None if no suitable time slot is found.
    """

    # Find available time slots on the given day
    available_time_slots = []
    current_time = datetime.strptime(f"{start_time}:00", "%H:%M")
    while current_time < datetime.strptime(f"{end_time}:00", "%H:%M"):
        # Check if the current time slot conflicts with Jennifer's schedule
        if not any(current_time < datetime.strptime(f"{schedule_end}:00", "%H:%M") and (current_time + timedelta(minutes=duration)).strftime('%H:%M') > datetime.strptime(f"{schedule_start}:00", "%H:%M") for schedule_start, schedule_end in schedules[day]):
            available_time_slots.append((current_time.strftime('%H:%M'), (current_time + timedelta(minutes=duration)).strftime('%H:%M')))
        current_time += timedelta(minutes=30)

    # If no suitable time slot is found, return None
    if not available_time_slots:
        return None

    # Check if John's preference can be satisfied
    for time_slot in available_time_slots:
        if time_slot[0] >= '14:30' and time_slot[1] <= '15:30':
            return time_slot[0], time_slot[1], day

    # If no suitable time slot is found, return the first available time slot
    return available_time_slots[0][0], available_time_slots[0][1], day


def main():
    # Define the existing schedules for John and Jennifer
    john_schedules = {
        'Monday': [],
        'Tuesday': [],
        'Wednesday': []
    }
    jennifer_schedules = {
        'Monday': [(9, 11), (11.5, 13), (13.5, 14.5), (15, 17)],
        'Tuesday': [(9, 11.5), (12, 17)],
        'Wednesday': [(9, 11.5), (12, 12.5), (13, 14), (14.5, 16), (16.5, 17)]
    }

    # Define the meeting duration and preferences
    meeting_duration = 30  # Meeting duration in minutes
    john_preferences = ['Monday after 14:30', 'Tuesday', 'Wednesday']

    # Find a suitable time for the meeting
    for day in ['Monday', 'Tuesday', 'Wednesday']:
        if day in john_preferences:
            continue
        start_time = 9
        end_time = 17
        if day == 'Monday':
            start_time = 11
        elif day == 'Tuesday':
            start_time = 11.5
        elif day == 'Wednesday':
            start_time = 11.5
        time_slot = find_meeting_time(int(start_time * 2), int(end_time * 2), meeting_duration, day, jennifer_schedules)
        if time_slot:
            print(f"{time_slot[0]}-{time_slot[1]} on {day}")
            break
    else:
        print("No suitable time slot found.")


if __name__ == "__main__":
    main()