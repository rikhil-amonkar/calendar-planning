from datetime import datetime, timedelta

def find_available_time(participants, meeting_duration):
    """
    Find a time that works for everyone's schedule and constraints.

    Args:
        participants (dict): A dictionary where keys are participant names and values are their schedules.
        meeting_duration (int): The duration of the meeting in minutes.

    Returns:
        tuple: A tuple containing the day of the week and the proposed time range in the format HH:MM-HH:MM.
    """

    # Get the day of the week
    day_of_week = datetime.now().weekday()
    if day_of_week == 0:
        day_of_week = "Monday"
    elif day_of_week == 1:
        day_of_week = "Tuesday"
    elif day_of_week == 2:
        day_of_week = "Wednesday"
    elif day_of_week == 3:
        day_of_week = "Thursday"
    elif day_of_week == 4:
        day_of_week = "Friday"
    elif day_of_week == 5:
        day_of_week = "Saturday"
    elif day_of_week == 6:
        day_of_week = "Sunday"

    # Sort the participants by their earliest available time
    sorted_participants = sorted(participants.items(), key=lambda x: x[1][0][0] if x[1] else datetime.max)

    # Initialize the proposed time to the earliest available time of the first participant
    proposed_time = [datetime.strptime(f"{datetime.now().strftime('%Y-%m-%d')} 09:00", "%Y-%m-%d %H:%M")]

    # Iterate over the participants to find a time that works for everyone
    while proposed_time:
        # Check if the proposed time conflicts with any participant's schedule
        conflict = False
        for participant, schedule in sorted_participants:
            for time in proposed_time:
                for start, end in schedule:
                    if start <= time + timedelta(minutes=meeting_duration) < end:
                        conflict = True
                        break
                if conflict:
                    break
            if conflict:
                break

        # If no conflict, return the proposed time
        if not conflict:
            return day_of_week, f"{proposed_time[0].strftime('%H:%M')}-{(proposed_time[0] + timedelta(minutes=meeting_duration)).strftime('%H:%M')}"

        # If conflict, increment the proposed time by 30 minutes and repeat the check
        # Also, consider other available times within the same 30-minute increment
        available_times = []
        for time in proposed_time:
            available_time = (time + timedelta(minutes=30)).replace(second=0, microsecond=0)
            while available_time < (time + timedelta(minutes=meeting_duration)).replace(second=0, microsecond=0):
                conflict = False
                for participant, schedule in sorted_participants:
                    for start, end in schedule:
                        if start <= available_time + timedelta(minutes=meeting_duration) < end:
                            conflict = True
                            break
                    if conflict:
                        break
                if not conflict:
                    available_times.append(available_time)
                available_time += timedelta(minutes=30)

        proposed_time = available_times

    # If no available time slot is found, return a message
    return day_of_week, "No available time slot found"

# Example usage:
participants = {
    "Eric": [],
    "Ashley": [(datetime.strptime("2024-07-22 10:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 10:30", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 11:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 12:00", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 12:30", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 13:00", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 15:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 16:00", "%Y-%m-%d %H:%M"))],
    "Ronald": [(datetime.strptime("2024-07-22 09:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 09:30", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 10:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 11:30", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 12:30", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 14:00", "%Y-%m-%d %H:%M")),
               (datetime.strptime("2024-07-22 14:30", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 17:00", "%Y-%m-%d %H:%M"))],
    "Larry": [(datetime.strptime("2024-07-22 09:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 12:00", "%Y-%m-%d %H:%M")),
              (datetime.strptime("2024-07-22 13:00", "%Y-%m-%d %H:%M"), datetime.strptime("2024-07-22 17:00", "%Y-%m-%d %H:%M"))]
}

meeting_duration = 30

day, time = find_available_time(participants, meeting_duration)
print(f"Day: {day}")
print(f"Time: {time}")