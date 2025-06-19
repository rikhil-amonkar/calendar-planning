from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        start_time (datetime): Start time of the day.
        end_time (datetime): End time of the day.
        duration (timedelta): Duration of the meeting.
        schedules (dict): Schedules of the participants.

    Returns:
        tuple: Proposed time and day of the week.
    """
    proposed_time = None
    for day in [start_time + timedelta(days=i) for i in range((end_time - start_time).days + 1)]:
        for hour in range(start_time.hour, end_time.hour):
            for minute in range(0, 60, 30):
                time = day.replace(hour=hour, minute=minute, second=0)
                if time + duration <= end_time:
                    conflict = False
                    for participant, schedule in schedules.items():
                        for block in schedule:
                            # Convert block times to datetime objects if they are integers
                            if isinstance(block[0], int) and isinstance(block[1], int):
                                block_start = datetime.combine(day.date(), datetime.min.time())
                                block_start = block_start.replace(hour=block[0], minute=block[1], second=0)
                                block_end = datetime.combine(day.date(), datetime.min.time())
                                block_end = block_end.replace(hour=block[1], minute=0, second=0)
                            else:
                                block_start = block[0]
                                block_end = block[1]
                            # Check if the proposed meeting conflicts with the schedule block
                            if (block_start <= time and time <= block_end) or (block_start <= time + duration and time + duration <= block_end):
                                conflict = True
                                break
                        if conflict:
                            break
                    if not conflict:
                        proposed_time = (time, time + duration)
                        break
            if proposed_time:
                break
        if proposed_time:
            break
    return proposed_time


def main():
    # Define the schedules
    schedules = {
        'Walter': [],
        'Cynthia': [(9, 9.5), (10, 10.5), (13.5, 14.5), (15, 16)],
        'Ann': [(10, 11), (13, 13.5), (14, 15), (16, 16.5)],
        'Catherine': [(9, 11.5), (12.5, 13.5), (14.5, 17)],
        'Kyle': [(9, 9.5), (10, 11.5), (12, 12.5), (13, 14.5), (15, 16)]
    }

    # Define the duration of the meeting
    duration = timedelta(minutes=30)

    # Define the start and end time of the day
    start_time = datetime(2024, 7, 29, 9, 0, 0)  # Monday
    end_time = datetime(2024, 7, 29, 17, 0, 0)

    # Find the proposed time
    proposed_time = find_meeting_time(start_time, end_time, duration, schedules)

    # Print the proposed time and day of the week
    if proposed_time:
        print(f"{proposed_time[0].strftime('%H:%M')} - {proposed_time[1].strftime('%H:%M')} {proposed_time[0].strftime('%A')}")
    else:
        print("No available time found.")


if __name__ == "__main__":
    main()