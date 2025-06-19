from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, schedules):
    """
    Find a time slot that works for all participants.

    Args:
    start_time (datetime): Start time of the day.
    end_time (datetime): End time of the day.
    duration (timedelta): Duration of the meeting.
    schedules (list): List of schedules for each participant.

    Returns:
    tuple: Proposed time range and day of the week.
    """
    # Initialize time slot
    time_slot = start_time

    # Loop through time slots
    while time_slot < end_time:
        # Check if time slot works for all participants
        if all(time_slot + duration <= schedule['end'] and time_slot >= schedule['start'] for schedule in schedules):
            return time_slot.strftime("%H:%M"), (time_slot + duration).strftime("%H:%M"), time_slot.strftime("%A")
        
        # Move to next time slot
        time_slot += timedelta(minutes=30)

    # If no time slot works, return None
    return None

def main():
    # Define schedules
    jeffrey_schedule = {'start': datetime(2024, 7, 22, 9, 30), 'end': datetime(2024, 7, 22, 11, 0)}
    virginia_schedule = [
        {'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 9, 30)},
        {'start': datetime(2024, 7, 22, 10, 0), 'end': datetime(2024, 7, 22, 10, 30)},
        {'start': datetime(2024, 7, 22, 14, 30), 'end': datetime(2024, 7, 22, 15, 0)},
        {'start': datetime(2024, 7, 22, 16, 0), 'end': datetime(2024, 7, 22, 16, 30)}
    ]
    melissa_schedule = [
        {'start': datetime(2024, 7, 22, 9, 0), 'end': datetime(2024, 7, 22, 11, 30)},
        {'start': datetime(2024, 7, 22, 12, 0), 'end': datetime(2024, 7, 22, 12, 30)},
        {'start': datetime(2024, 7, 22, 13, 0), 'end': datetime(2024, 7, 22, 15, 0)},
        {'start': datetime(2024, 7, 22, 16, 0), 'end': datetime(2024, 7, 22, 17, 0)}
    ]

    # Define meeting duration
    duration = timedelta(minutes=30)

    # Find meeting time
    meeting_time = find_meeting_time(datetime(2024, 7, 22, 9, 0), datetime(2024, 7, 22, 17, 0), duration, [jeffrey_schedule, virginia_schedule, melissa_schedule])

    # Print meeting time
    if meeting_time:
        print(f"Meeting time: {meeting_time[0]}-{meeting_time[1]} on {meeting_time[2]}")
    else:
        print("No meeting time found.")

if __name__ == "__main__":
    main()