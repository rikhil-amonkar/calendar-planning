from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (datetime): The start of the day.
    end_time (datetime): The end of the day.
    duration (int): The duration of the meeting in minutes.
    schedules (dict): A dictionary of schedules where each key is a person's name
                      and each value is a list of tuples representing the time
                      ranges they are busy.

    Returns:
    str: A string representing the proposed time in the format HH:MM-HH:MM on the day of the week.
    """
    # Input validation
    if duration <= 0:
        raise ValueError("Meeting duration must be greater than 0")

    if not isinstance(schedules, dict):
        raise ValueError("Schedules must be a dictionary")

    # Generate all possible time slots
    time_slots = []
    current_time = start_time
    while current_time < end_time:
        time_slots.append((current_time, current_time + timedelta(minutes=duration)))
        current_time += timedelta(minutes=30)

    # Filter out the time slots that do not work for anyone
    working_time_slots = []
    for time_slot in time_slots:
        works_for_everyone = True
        for person, busy_times in schedules.items():
            for busy_time in busy_times:
                if busy_time[0] < time_slot[1] and busy_time[1] > time_slot[0]:
                    # Check if the conflict is due to the entire meeting duration
                    if (busy_time[1] - busy_time[0]) >= timedelta(minutes=duration):
                        works_for_everyone = False
                        break
            if not works_for_everyone:
                break
        if works_for_everyone:
            working_time_slots.append(time_slot)

    # If no time slots work for everyone, return a message indicating that
    if not working_time_slots:
        return "No time slot works for everyone."

    # Return the first working time slot
    start_time_str = working_time_slots[0][0].strftime("%H:%M")
    end_time_str = working_time_slots[0][1].strftime("%H:%M")
    day_of_week = working_time_slots[0][0].strftime("%A")
    return f"{start_time_str}-{end_time_str} on {day_of_week}"

def print_proposed_time(proposed_time):
    """
    Print the proposed time in a formatted string.

    Args:
    proposed_time (str): The proposed time in the format HH:MM-HH:MM on the day of the week.
    """
    print(f"Proposed time: {proposed_time}")

def main():
    # Define the existing schedules
    schedules = {
        "Christine": [(datetime(2024, 7, 22, 11, 0), datetime(2024, 7, 22, 11, 30)),
                      (datetime(2024, 7, 22, 15, 0), datetime(2024, 7, 22, 15, 30))],
        "Helen": [(datetime(2024, 7, 22, 9, 30), datetime(2024, 7, 22, 10, 30)),
                  (datetime(2024, 7, 22, 11, 0), datetime(2024, 7, 22, 11, 30)),
                  (datetime(2024, 7, 22, 12, 0), datetime(2024, 7, 22, 12, 30)),
                  (datetime(2024, 7, 22, 13, 30), datetime(2024, 7, 22, 16, 0)),
                  (datetime(2024, 7, 22, 16, 30), datetime(2024, 7, 22, 17, 0))]
    }

    # Define the meeting duration
    duration = 30

    # Define the day of the week
    day_of_week = "Monday"

    # Find a time that works for everyone
    start_time = datetime(2024, 7, 22, 9, 0)
    end_time = datetime(2024, 7, 22, 17, 0)
    proposed_time = find_meeting_time(start_time, end_time, duration, schedules)

    # Print the proposed time
    print_proposed_time(proposed_time)

if __name__ == "__main__":
    main()