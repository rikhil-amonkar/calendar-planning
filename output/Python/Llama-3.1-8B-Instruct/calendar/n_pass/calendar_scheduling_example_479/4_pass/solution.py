from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, duration, participants):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (str): Start time of the day in HH:MM format.
    end_time (str): End time of the day in HH:MM format.
    duration (int): Duration of the meeting in minutes.
    participants (dict): Dictionary of participants with their schedules.

    Returns:
    str: Proposed time in HH:MM:HH:MM format.
    """
    # Convert start and end times to minutes
    start_minutes = int(start_time[:2]) * 60 + int(start_time[3:])
    end_minutes = int(end_time[:2]) * 60 + int(end_time[3:])

    # Iterate over possible meeting times
    for hour in range(start_minutes // 60, end_minutes // 60):
        for minute in range(0, 60):
            # Convert time to minutes
            meeting_minutes = hour * 60 + minute

            # Check if meeting time is available for all participants
            if all(
                not (start <= meeting_minutes < end)
                for schedule in participants.values()
                for start, end in schedule
            ):
                # Convert meeting time back to HH:MM format
                meeting_start = datetime(2024, 1, 1, hour, minute).strftime("%H:%M")
                meeting_end = (datetime(2024, 1, 1, hour, minute) + timedelta(minutes=duration)).strftime("%H:%M")

                return f"{meeting_start}:{meeting_end} on {datetime(2024, 1, 1).strftime('%A')}"

    # If no meeting time is found, return a message
    return "No meeting time found"


def main():
    # Define participants' schedules
    participants = {
        "Evelyn": [],
        "Joshua": [(11 * 60 + 0, 12 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30), (16 * 60 + 30, 17 * 60)],
        "Kevin": [],
        "Gerald": [],
        "Jerry": [
            (9 * 60 + 0, 9 * 60 + 30),
            (10 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (13 * 60 + 30, 14 * 60),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60)
        ],
        "Jesse": [
            (9 * 60 + 0, 9 * 60 + 30),
            (10 * 60 + 30, 12 * 60),
            (12 * 60 + 30, 13 * 60),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60 + 30)
        ],
        "Kenneth": [
            (10 * 60 + 30, 12 * 60 + 30),
            (13 * 60 + 30, 14 * 60),
            (14 * 60 + 30, 15 * 60),
            (15 * 60 + 30, 16 * 60),
            (16 * 60 + 30, 17 * 60)
        ]
    }

    # Define meeting duration
    duration = 60  # 1 hour

    # Define work hours
    start_time = "09:00"
    end_time = "17:00"

    # Find a meeting time that works for everyone
    meeting_time = find_meeting_time(start_time, end_time, duration, participants)

    # Print the meeting time
    print(meeting_time)


if __name__ == "__main__":
    main()