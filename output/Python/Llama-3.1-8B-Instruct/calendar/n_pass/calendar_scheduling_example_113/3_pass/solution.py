from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules, unavailable_time_slot):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (datetime): The start time of the day.
        end_time (datetime): The end time of the day.
        duration (int): The duration of the meeting in minutes.
        schedules (dict): A dictionary of participants and their schedules.
        unavailable_time_slot (tuple): The unavailable time slot.

    Returns:
        tuple: A proposed time and the day of the week.
    """
    # Check if the unavailable time slot conflicts with the start time
    if unavailable_time_slot[0] <= start_time.hour * 60 + start_time.minute < unavailable_time_slot[1]:
        return None

    # Find the earliest available time slot
    for hour in range(start_time.hour, end_time.hour):
        for minute in range(0, 60, duration):
            time = start_time.replace(hour=hour, minute=minute)
            # Check if the time slot is available for all participants
            is_available = True
            for participant, schedule in schedules.items():
                # Check if the time slot conflicts with any of the participant's schedules
                for schedule_time in schedule:
                    if (time + timedelta(minutes=duration)).minute >= schedule_time[0] and (time + timedelta(minutes=duration)).minute < schedule_time[1]:
                        is_available = False
                        break
                if not is_available:
                    break
            # Check if the time slot conflicts with the unavailable time slot
            if time.hour * 60 + time.minute >= unavailable_time_slot[0] and time.hour * 60 + time.minute < unavailable_time_slot[1]:
                is_available = False
            if is_available:
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

    # Define the unavailable time slot
    unavailable_time_slot = (9*60, 9*60+30)

    # Find a proposed time and the day of the week
    proposed_time = find_meeting_time(start_time, end_time, duration, schedules, unavailable_time_slot)

    # Print the proposed time and the day of the week
    if proposed_time:
        print(f"{proposed_time[0]} - {proposed_time[1]} on {proposed_time[2]}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()