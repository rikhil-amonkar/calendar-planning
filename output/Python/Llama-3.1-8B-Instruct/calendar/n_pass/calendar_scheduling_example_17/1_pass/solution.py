from datetime import datetime, timedelta

def schedule_meeting(margaret_schedule, donna_schedule, helen_schedule, meeting_duration, day_of_week, helen_preference):
    """
    Schedules a meeting for Margaret, Donna, and Helen based on their schedules and constraints.

    Args:
    - margaret_schedule (list): Margaret's blocked calendar slots.
    - donna_schedule (list): Donna's blocked calendar slots.
    - helen_schedule (list): Helen's blocked calendar slots.
    - meeting_duration (int): The duration of the meeting in minutes.
    - day_of_week (str): The day of the week for the meeting.
    - helen_preference (str): Helen's preference for meeting time.

    Returns:
    - proposed_time (str): A proposed time for the meeting in the format HH:MM-HH:MM.
    """
    # Sort the schedules by start time
    margaret_schedule.sort(key=lambda x: x[0])
    donna_schedule.sort(key=lambda x: x[0])
    helen_schedule.sort(key=lambda x: x[0])

    # Initialize the current time to 9:00
    current_time = datetime.strptime(f"09:00", "%H:%M")

    # Loop until we find a time that works for everyone
    while current_time.hour < 17:
        # Check if the current time works for Margaret
        if not any((current_time >= start and current_time < end) for start, end in margaret_schedule):
            # Check if the current time works for Donna
            if not any((current_time >= start and current_time < end) for start, end in donna_schedule):
                # Check if the current time works for Helen
                if not any((current_time >= start and current_time < end) for start, end in helen_schedule):
                    # Check if Helen's preference is met
                    if current_time.hour < 13:
                        # Check if the meeting can fit in the remaining time
                        end_time = current_time + timedelta(minutes=meeting_duration)
                        if end_time.hour < 17:
                            # Return the proposed time
                            return f"{day_of_week}: {current_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}"

        # Increment the current time by 30 minutes
        current_time += timedelta(minutes=30)

    # If no time is found, return a message
    return f"No time found for meeting on {day_of_week}."

# Example usage
margaret_schedule = [(9, 10), (10.5, 11), (11.5, 12), (13, 13.5), (15, 15.5)]
donna_schedule = [(14.5, 15), (16, 16.5)]
helen_schedule = [(9, 9.5), (10, 11.5), (13, 14), (14.5, 15), (15.5, 17)]
meeting_duration = 30
day_of_week = "Monday"
helen_preference = "before 13:30"

print(schedule_meeting(margaret_schedule, donna_schedule, helen_schedule, meeting_duration, day_of_week, helen_preference))