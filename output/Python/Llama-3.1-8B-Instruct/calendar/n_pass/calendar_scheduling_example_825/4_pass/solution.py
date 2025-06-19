from datetime import datetime, timedelta

def find_available_time(laura_schedule, philip_schedule, day, duration):
    """
    Find a time that works for both Laura and Philip's schedules.

    Args:
    - laura_schedule (dict): Laura's schedule for the day.
    - philip_schedule (dict): Philip's schedule for the day.
    - day (str): The day of the week (e.g., Monday, Tuesday).
    - duration (int): The duration of the meeting in minutes.

    Returns:
    - A tuple containing the start and end times of the meeting in HH:MM format.
    """
    # Filter the schedules for the given day
    laura_day_schedule = laura_schedule.get(day, {})
    philip_day_schedule = philip_schedule.get(day, {})

    # Sort the schedules by start time
    laura_day_schedule = dict(sorted(laura_day_schedule.items()))
    philip_day_schedule = dict(sorted(philip_day_schedule.items()))

    # Initialize the start and end times
    start_time = None
    end_time = None

    # Iterate over the day to find a time that works for both
    for time, end in laura_day_schedule.items():
        # Convert time and end to datetime objects for comparison
        time = datetime.strptime(time, "%H:%M")
        end = datetime.strptime(end, "%H:%M")

        # Check if Philip is available during this time
        philip_available = True
        for start, philip_end in philip_day_schedule.items():
            philip_start = datetime.strptime(start, "%H:%M")
            philip_end = datetime.strptime(philip_end, "%H:%M")
            if (philip_start <= time < philip_end) or (philip_start < end <= philip_end):
                philip_available = False
                break

        if philip_available:
            # Check if the time is long enough for the meeting
            if end - time >= timedelta(minutes=duration):
                # Update the start and end times
                start_time = time.strftime("%H:%M")
                end_time = (time + timedelta(minutes=duration)).strftime("%H:%M")
                break

    return start_time, end_time


def main():
    # Define the schedules
    laura_schedule = {
        "Monday": ["10:30", "11:00", "12:30", "13:00", "14:30", "15:30", "16:00", "17:00"],
        "Tuesday": ["9:30", "10:00", "11:00", "11:30", "13:00", "13:30", "14:30", "15:00", "16:00", "17:00"],
        "Wednesday": ["11:30", "12:00", "12:30", "13:00", "15:30", "16:30"],
        "Thursday": ["10:30", "12:00", "13:30", "15:00", "15:30", "16:00", "16:30"]
    }
    philip_schedule = {
        "Monday": ["9:00", "17:00"],
        "Tuesday": ["9:00", "11:00", "11:30", "13:00", "13:30", "14:00", "14:30", "15:00", "16:30"],
        "Wednesday": ["9:00", "10:00", "11:00", "12:00", "12:30", "16:00", "16:30", "17:00"],
        "Thursday": ["9:00", "10:30", "11:00", "12:30", "13:00", "17:00"]
    }

    # Define the meeting duration
    duration = 60  # 1 hour

    # Find a time that works for both
    for day in ["Monday", "Tuesday", "Wednesday", "Thursday"]:
        if day!= "Wednesday":  # Philip can't meet on Wednesday
            start_time, end_time = find_available_time(laura_schedule, philip_schedule, day, duration)
            if start_time:
                print(f"{day}, {start_time}:{end_time}")


if __name__ == "__main__":
    main()