from datetime import datetime, timedelta

def find_available_time(start_time, end_time, busy_times):
    """
    Find a time slot that is not busy.
    
    Args:
    start_time (datetime): The start time of the day.
    end_time (datetime): The end time of the day.
    busy_times (list): A list of busy times.
    
    Returns:
    tuple: A tuple containing the start and end time of the available time slot.
    """
    available_time = None
    for time in [start_time + timedelta(minutes=i) for i in range((end_time - start_time).seconds // 60 + 1)]:
        if time not in busy_times:
            if available_time is None:
                available_time = (time, time + timedelta(minutes=30))
            else:
                available_time = (available_time[0], time + timedelta(minutes=30))
        else:
            if available_time is not None:
                return available_time
    return available_time

def find_meeting_time(day, busy_times):
    """
    Find a time that works for everyone's schedule and constraints.
    
    Args:
    day (str): The day of the week.
    busy_times (dict): A dictionary of busy times for each person.
    
    Returns:
    tuple: A tuple containing the start and end time of the meeting.
    """
    start_time = datetime.strptime(f"{day} 09:00", "%A %H:%M")
    end_time = datetime.strptime(f"{day} 17:00", "%A %H:%M")
    
    janice_preferences = [datetime.strptime(f"{day} 13:00", "%A %H:%M) + timedelta(minutes=i) for i in range(90)]
    
    for time in janice_preferences:
        if find_available_time(time, end_time, busy_times["Janice"]):
            return (time.strftime("%H:%M"), (time + timedelta(minutes=30)).strftime("%H:%M"))

    return find_available_time(start_time, end_time, busy_times["Janice"])

def main():
    day = "Monday"
    busy_times = {
        "Christine": [
            datetime.strptime("09:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("10:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("12:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("12:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("14:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60
        ],
        "Janice": [],
        "Bobby": [
            datetime.strptime("12:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("12:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("14:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60
        ],
        "Elizabeth": [
            datetime.strptime("09:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("09:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("11:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("14:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("17:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60
        ],
        "Tyler": [
            datetime.strptime("09:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("11:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("12:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("12:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("13:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("17:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60
        ],
        "Edward": [
            datetime.strptime("09:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("09:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("10:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("11:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("11:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("14:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("14:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("15:30", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("16:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60,
            datetime.strptime("17:00", "%H:%M") + datetime.strptime(day, "%A").weekday() * 24 * 60 * 60
        ]
    }
    
    meeting_time = find_meeting_time(day, busy_times)
    print(f"The meeting time is {meeting_time[0]} to {meeting_time[1]} on {day}.")

if __name__ == "__main__":
    main()