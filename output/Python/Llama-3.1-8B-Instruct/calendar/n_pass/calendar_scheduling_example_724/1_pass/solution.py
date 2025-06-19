from datetime import datetime, timedelta

def find_meeting_time(available_days, meeting_duration, constraints):
    """
    Find a suitable time for a meeting based on the participants' schedules and constraints.

    Args:
        available_days (list): List of days of the week (Monday, Tuesday, Wednesday)
        meeting_duration (int): Duration of the meeting in minutes
        constraints (dict): Dictionary of constraints for each participant

    Returns:
        tuple: Proposed meeting time in the format HH:MM and day of the week
    """
    # Convert meeting duration from minutes to hours and minutes
    meeting_duration_hours = meeting_duration // 60
    meeting_duration_minutes = meeting_duration % 60

    # Iterate over each available day
    for day in available_days:
        # Iterate over each hour in the day
        for hour in range(9, 17):
            # Iterate over each minute in the hour
            for minute in range(0, 60, 30):
                # Create a start time for the meeting
                start_time = datetime.strptime(f"{day} {hour:02d}:{minute:02d}", "%A %H:%M")

                # Calculate the end time for the meeting
                end_time = start_time + timedelta(hours=meeting_duration_hours, minutes=meeting_duration_minutes)

                # Check if the meeting time is available for both participants
                if (day not in constraints.get("Tyler", []) or
                        start_time not in constraints.get("Tyler", []) and
                        end_time not in constraints.get("Tyler", [])) and (
                        day not in constraints.get("Ruth", []) or
                        start_time not in constraints.get("Ruth", []) and
                        end_time not in constraints.get("Ruth", [])):
                    # Check if Tyler wants to avoid meetings before 16:00 on Monday
                    if day == "Monday" and hour < 16 and start_time < datetime.strptime("Monday 16:00", "%A %H:%M"):
                        continue

                    # Return the proposed meeting time
                    return f"{start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')} {day}"

    # If no meeting time is found, return an error message
    return "No meeting time found"

# Define the constraints for each participant
constraints = {
    "Tyler": [
        datetime.strptime("2022-01-04 09:00", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 09:30", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-04 14:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 15:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-05 10:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-05 11:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-05 12:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-05 13:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-05 13:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-05 14:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-05 16:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-05 17:00", "%Y-%m-%d %H:%M"),
    ],
    "Ruth": [
        datetime.strptime("2022-01-04 09:00", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 10:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-04 10:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 12:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-04 12:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 14:30", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-04 15:00", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 16:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-04 16:30", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-04 17:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-05 09:00", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-05 17:00", "%Y-%m-%d %H:%M"),
        datetime.strptime("2022-01-06 09:00", "%Y-%m-%d %H:%M"): datetime.strptime("2022-01-06 17:00", "%Y-%m-%d %H:%M"),
    ]
}

# Define the available days and meeting duration
available_days = ["Monday", "Tuesday", "Wednesday"]
meeting_duration = 30

# Find a suitable meeting time
proposed_time = find_meeting_time(available_days, meeting_duration, constraints)

# Print the proposed meeting time
print(proposed_time)