from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (datetime): The start time of the day.
        end_time (datetime): The end time of the day.
        duration (int): The duration of the meeting in minutes.
        schedules (dict): A dictionary of participants and their schedules.

    Returns:
        tuple: A proposed time and the day of the week.
    """
    # Find the earliest available time slot
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, duration):
            time = start_time.replace(hour=hour, minute=minute)
            if all(time + timedelta(minutes=duration) > schedule[0] and time < schedule[1] for schedule in schedules[participant] for participant in schedules):
                return time.strftime("%H:%M"), (time + timedelta(minutes=duration)).strftime("%H:%M"), start_time.strftime("%A")

def main():
    # Define the schedules for each participant
    schedules = {
        "Bradley": [(9*60+30, 10*60), (12*60+30, 13*60), (13*60+30, 14*60), (15*60+30, 16*60)],
        "Teresa": [(10*60+30, 11*60), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 15*60)],
        "Elizabeth": [(9*60, 9*60+30), (10*60+30, 11*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (15*60+30, 17*60)],
        "Christian": [(9*60, 9*60+30), (10*60+30, 17*60)]
    }

    # Define the meeting duration
    duration = 30

    # Define the start and end time of the day
    start_time = datetime(2024, 7, 22, 9, 0)
    end_time = datetime(2024, 7, 22, 17, 0)

    # Find a proposed time and the day of the week
    proposed_time, end_time, day_of_week = find_meeting_time(start_time, end_time, duration, schedules)

    # Print the proposed time and the day of the week
    print(f"{proposed_time}:{end_time} on {day_of_week}")

if __name__ == "__main__":
    main()