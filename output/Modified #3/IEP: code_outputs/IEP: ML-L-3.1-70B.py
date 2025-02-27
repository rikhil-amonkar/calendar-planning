def find_available_time(work_hours, busy_times, meeting_duration):
    """
    Find the earliest available time slot for a meeting.

    Args:
    work_hours (tuple): Start and end time of the work hours.
    busy_times (list): List of tuples representing the start and end times of busy periods.
    meeting_duration (int): Duration of the meeting in minutes.

    Returns:
    tuple: Start and end time of the earliest available time slot.
    """
    start_time = work_hours[0]
    for busy_time in busy_times:
        end_time = busy_time[0]
        if end_time - start_time >= meeting_duration:
            return (start_time, start_time + meeting_duration)
        start_time = busy_time[1]
    end_time = work_hours[1]
    if end_time - start_time >= meeting_duration:
        return (start_time, start_time + meeting_duration)
    return None


def main():
    work_hours = (9 * 60, 17 * 60)  # Convert hours to minutes
    busy_times = [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), 
                  (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 14 * 60 + 30), 
                  (15 * 60, 16 * 60 + 30)]  # Convert hours to minutes
    meeting_duration = 30

    available_time = find_available_time(work_hours, busy_times, meeting_duration)
    if available_time:
        start_hour, start_minute = divmod(available_time[0], 60)
        end_hour, end_minute = divmod(available_time[1], 60)
        print(f"Here is the proposed time: Monday, {start_hour}:{start_minute:02d} - {end_hour}:{end_minute:02d}")
    else:
        print("No available time slot found.")


if __name__ == "__main__":
    main()