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
    sorted_participants = sorted(participants.items(), key=lambda x: min([t[0] for t in x[1]]))

    # Initialize the proposed time to the earliest available time of the first participant
    proposed_time = [datetime.strptime(f"{datetime.now().strftime('%Y-%m-%d')} 09:00", "%Y-%m-%d %H:%M")]

    # Iterate over the participants to find a time that works for everyone
    for participant, schedule in sorted_participants:
        # Find the first available time slot that is at least meeting_duration minutes long
        for time in proposed_time:
            for s in schedule:
                if s[0] >= time.strftime("%H:%M") and s[1] <= (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    continue
                elif s[0] >= time.strftime("%H:%M") and s[1] > (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    proposed_time.append(time + timedelta(minutes=s[0].time().minute))
                    break
                elif s[0] > time.strftime("%H:%M") and s[0] < (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    proposed_time.append(time + timedelta(minutes=s[0].time().minute))
                    break
                elif s[0] > time.strftime("%H:%M") and s[0] > (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    proposed_time.append(time + timedelta(minutes=s[0].time().minute))
                    break
                elif s[1] <= time.strftime("%H:%M") and s[1] < (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    proposed_time.append(time + timedelta(minutes=s[1].time().minute))
                    break
                elif s[1] > time.strftime("%H:%M") and s[1] > (time + timedelta(minutes=meeting_duration)).strftime("%H:%M"):
                    proposed_time.append(time + timedelta(minutes=s[1].time().minute))
                    break
                else:
                    proposed_time.append(time + timedelta(minutes=meeting_duration))
                    break
            else:
                continue
            break
        else:
            continue
        break

    # Return the day of the week and the proposed time range
    return day_of_week, f"{proposed_time[0].strftime('%H:%M')}-{(proposed_time[0] + timedelta(minutes=meeting_duration)).strftime('%H:%M')}"

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