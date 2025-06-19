from datetime import datetime, timedelta

def find_meeting_time(schedule_a, schedule_n, duration, day, preferences, unavailable_slots):
    """
    Find a suitable time for a meeting between two participants.

    Args:
    schedule_a (list): Amanda's schedule.
    schedule_n (list): Nathan's schedule.
    duration (int): Meeting duration in minutes.
    day (str): Day of the week (e.g., Monday, Tuesday).
    preferences (dict): Preferences for meeting time.
    unavailable_slots (list): List of unavailable time slots.

    Returns:
    tuple: Proposed meeting time and day of the week.
    """
    # Convert schedules to datetime objects
    schedule_a = [datetime.strptime(f"{day} {time}", f"%A %H:%M") for time in schedule_a]
    schedule_n = [datetime.strptime(f"{day} {time}", f"%A %H:%M") for time in schedule_n]

    # Filter schedules based on preferences
    if day == "Monday":
        schedule_a = [t for t in schedule_a if t >= datetime.strptime("Monday 09:00", "%A %H:%M") and t < datetime.strptime("Monday 17:00", "%A %H:%M")]
        schedule_n = [t for t in schedule_n if t >= datetime.strptime("Monday 09:00", "%A %H:%M") and t < datetime.strptime("Monday 17:00", "%A %H:%M")]
    else:
        schedule_a = [t for t in schedule_a if t >= datetime.strptime("Tuesday 09:00", "%A %H:%M") and t < datetime.strptime("Tuesday 17:00", "%A %H:%M")]
        schedule_n = [t for t in schedule_n if t >= datetime.strptime("Tuesday 09:00", "%A %H:%M") and t < datetime.strptime("Tuesday 17:00", "%A %H:%M")]

    # Filter schedules based on Amanda's preference
    schedule_a = [t for t in schedule_a if t.hour > 11]

    # Filter Nathan's schedule based on his preference
    schedule_n = [t for t in schedule_n if t.hour > 11]

    # Filter out unavailable time slots
    unavailable_slots = [datetime.strptime(f"{day} {time}", f"%A %H:%M") for time in unavailable_slots]
    schedule_a = [t for t in schedule_a if t not in unavailable_slots]
    schedule_n = [t for t in schedule_n if t not in unavailable_slots]

    # Find available time slots for Amanda
    available_slots_a = []
    for i in range(len(schedule_a) - 1):
        start = schedule_a[i]
        end = schedule_a[i + 1]
        available_slots_a.append((start, end))

    # Find available time slots for Nathan
    available_slots_n = []
    for i in range(len(schedule_n) - 1):
        start = schedule_n[i]
        end = schedule_n[i + 1]
        available_slots_n.append((start, end))

    # Find a slot that works for both participants
    for start_a, end_a in available_slots_a:
        for start_n, end_n in available_slots_n:
            # Check if the slot is within Nathan's available slots
            if start_a >= start_n and end_a <= end_n:
                # Check if the slot is long enough for the meeting
                if (end_a - start_a).total_seconds() / 60 >= duration:
                    return start_a.strftime("%H:%M"), end_a.strftime("%H:%M"), day

    # If no slot is found, return an error message
    return "No available time slot found."

def main():
    schedule_a = ["09:00", "10:30", "11:00", "11:30", "12:30", "13:00", "13:30", "14:00", "14:30", "15:00", "09:30", "10:00", "10:30", "11:30", "12:00", "13:30", "14:30", "15:30", "16:00", "16:30", "17:00"]
    schedule_n = ["09:00", "10:00", "10:30", "11:00", "11:30", "13:30", "14:30", "16:00", "16:30", "09:30", "10:30", "11:00", "13:00", "13:30", "14:00", "14:30", "15:30", "16:00", "16:30"]
    duration = 30
    day = "Monday"
    preferences = {"Amanda": {"day": "Tuesday", "time": "after 11:00"}, "Nathan": {"day": "Monday", "time": ""}}
    unavailable_slots = ["00:00", "01:00", "02:00", "03:00", "04:00", "05:00", "06:00", "07:00", "08:00", "23:00", "24:00"]

    proposed_time = find_meeting_time(schedule_a, schedule_n, duration, day, preferences, unavailable_slots)
    print(f"Proposed meeting time: {proposed_time[0]} - {proposed_time[1]} on {proposed_time[2]}")

if __name__ == "__main__":
    main()