from datetime import datetime, timedelta

def find_meeting_time(start_time, end_time, participants, duration):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
    start_time (datetime): The start of the work hours (Monday, 9:00).
    end_time (datetime): The end of the work hours (Monday, 17:00).
    participants (list): A list of participants and their schedules.
    duration (int): The duration of the meeting in minutes.

    Returns:
    tuple: A proposed time range (start, end) and the day of the week.
    """
    # Convert duration from minutes to hours and minutes
    meeting_duration = timedelta(hours=duration // 60, minutes=duration % 60)

    # Iterate over possible meeting times
    for hour in range(9, 17):
        for minute in range(0, 60):
            meeting_time = datetime(int(datetime.now().year), 1, 1, hour, minute)
            meeting_time = meeting_time.replace(day=29)
            if meeting_time + meeting_duration <= end_time:
                # Check if the meeting time works for all participants
                if all(
                    not (meeting_time + meeting_duration).time() in participant["busy"]
                    for participant in participants
                    for busy in participant.get("busy", [])
                ):
                    # Check if Margaret wants to avoid meeting on Monday before 14:30
                    if meeting_time < datetime(int(datetime.now().year), 1, 29, 14, 30, 0):
                        continue
                    return meeting_time.strftime("%H:%M"), (meeting_time + meeting_duration).strftime("%H:%M"), "Monday"

    # If no meeting time is found, return an error message
    return "No meeting time found", "No meeting time found", "No day"

def main():
    # Define the existing schedules for everyone during the day
    participants = [
        {"name": "Shirley", "busy": [
            ["Monday", "10:30", "11:00"],
            ["Monday", "12:00", "12:30"]
        ]},
        {"name": "Jacob", "busy": [
            ["Monday", "9:00", "9:30"],
            ["Monday", "10:00", "10:30"],
            ["Monday", "11:00", "11:30"],
            ["Monday", "12:30", "13:30"],
            ["Monday", "14:30", "15:00"]
        ]},
        {"name": "Stephen", "busy": [
            ["Monday", "11:30", "12:00"],
            ["Monday", "12:30", "13:00"]
        ]},
        {"name": "Margaret", "busy": [
            ["Monday", "9:00", "9:30"],
            ["Monday", "10:30", "12:30"],
            ["Monday", "13:00", "13:30"],
            ["Monday", "15:00", "15:30"],
            ["Monday", "16:30", "17:00"]
        ]},
        {"name": "Mason", "busy": [
            ["Monday", "9:00", "10:00"],
            ["Monday", "10:30", "11:00"],
            ["Monday", "11:30", "12:30"],
            ["Monday", "13:00", "13:30"],
            ["Monday", "14:00", "14:30"],
            ["Monday", "16:30", "17:00"]
        ]}
    ]

    # Define the work hours and meeting duration
    start_time = datetime(2024, 7, 29, 9, 0, 0)
    end_time = datetime(2024, 7, 29, 17, 0, 0)
    duration = 30

    # Find a meeting time that works for everyone's schedule and constraints
    proposed_time, end_time_str, day = find_meeting_time(start_time, end_time, participants, duration)

    # Print the proposed meeting time and day
    print(f"Proposed meeting time: {proposed_time}:{end_time_str} on {day}")

if __name__ == "__main__":
    main()