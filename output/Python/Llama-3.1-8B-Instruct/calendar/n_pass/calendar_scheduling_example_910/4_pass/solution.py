from datetime import datetime, timedelta

def find_meeting_time(bryan_schedule, nicholas_schedule, meeting_duration, preferred_days=None):
    """
    Find a suitable time for a meeting between two participants.

    Args:
    bryan_schedule (list): Bryan's schedule as a list of tuples (day, start_time, end_time)
    nicholas_schedule (list): Nicholas's schedule as a list of tuples (day, start_time, end_time)
    meeting_duration (int): The duration of the meeting in minutes
    preferred_days (list, optional): A list of preferred days for the meeting. Defaults to None.

    Returns:
    tuple: A tuple containing the day of the week and the proposed time range for the meeting.
    """
    # Define the work hours and days
    work_hours = [9, 17]
    work_days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Filter the schedules to only include the preferred days
    if preferred_days:
        bryan_schedule = [(day, start, end) for day, start, end in bryan_schedule if day in preferred_days]
        nicholas_schedule = [(day, start, end) for day, start, end in nicholas_schedule if day in preferred_days]

    # Validate the input schedules
    if not bryan_schedule or not nicholas_schedule:
        return None

    # Validate the meeting duration
    if meeting_duration <= 0:
        return None

    # Check if the preferred days are a subset of the work days
    for day in preferred_days:
        if day not in work_days:
            return None

    # Find the overlapping time slots for both participants
    overlapping_slots = []
    for day in work_days:
        if day in preferred_days:
            bryan_slots = [(start, end) for _, start, end in bryan_schedule if day == _]
            nicholas_slots = [(start, end) for _, start, end in nicholas_schedule if day == _]

            # Sort the time slots by start time
            bryan_slots.sort()
            nicholas_slots.sort()

            # Find the overlapping time slots
            i = j = 0
            while i < len(bryan_slots) and j < len(nicholas_slots):
                bryan_start, bryan_end = bryan_slots[i]
                nicholas_start, nicholas_end = nicholas_slots[j]

                # Check if the time slots overlap
                if bryan_start < nicholas_end and nicholas_start < bryan_end:
                    # Find the overlapping time
                    overlap_start = max(bryan_start, nicholas_start)
                    overlap_end = min(bryan_end, nicholas_end)

                    # Check if the overlapping time is long enough for the meeting
                    if (overlap_end - overlap_start) >= meeting_duration:
                        overlapping_slots.append((day, overlap_start, overlap_end))

                # Move to the next time slot
                if bryan_start < nicholas_start:
                    i += 1
                else:
                    j += 1

    # Find the first available time slot that is long enough for the meeting
    for day, start, end in overlapping_slots:
        if start >= work_hours[0] * 60 and end <= work_hours[1] * 60:
            return day, (start, end)

    # If no time slot is available, return None
    return None


# Define the schedules
bryan_schedule = [
    ('Thursday', 9*60, 10*60),
    ('Thursday', 12*60*60 + 30*60, 13*60*60 + 30*60),
    ('Friday', 10*60*60 + 30*60, 11*60*60),
    ('Friday', 14*60*60, 14*60*60 + 30*60)
]
nicholas_schedule = [
    ('Monday', 11*60*60 + 30*60, 12*60*60),
    ('Monday', 13*60*60, 15*60*60 + 30*60),
    ('Tuesday', 9*60*60, 9*60*60 + 30*60),
    ('Tuesday', 11*60*60, 13*60*60 + 30*60),
    ('Tuesday', 14*60*60, 16*60*60 + 30*60),
    ('Wednesday', 9*60*60, 9*60*60 + 30*60),
    ('Wednesday', 10*60*60, 11*60*60),
    ('Wednesday', 11*60*60 + 30*60, 13*60*60 + 30*60),
    ('Wednesday', 14*60*60, 14*60*60 + 30*60),
    ('Wednesday', 15*60*60, 16*60*60 + 30*60),
    ('Thursday', 10*60*60 + 30*60, 11*60*60 + 30*60),
    ('Thursday', 12*60*60, 12*60*60 + 30*60),
    ('Thursday', 15*60*60, 15*60*60 + 30*60),
    ('Thursday', 16*60*60 + 30*60, 17*60*60),
    ('Friday', 9*60*60, 10*60*60 + 30*60),
    ('Friday', 11*60*60, 12*60*60),
    ('Friday', 12*60*60 + 30*60, 14*60*60 + 30*60),
    ('Friday', 15*60*60 + 30*60, 16*60*60),
    ('Friday', 16*60*60 + 30*60, 17*60*60)
]

# Define the meeting duration
meeting_duration = 60  # 1 hour

# Define the preferred days
preferred_days = ['Monday', 'Tuesday', 'Wednesday', 'Friday']

# Find the meeting time
meeting_time = find_meeting_time(bryan_schedule, nicholas_schedule, meeting_duration, preferred_days)
if meeting_time:
    day, (start, end) = meeting_time
    start_time = datetime.strptime(f"{start//60:02d}:{start%60:02d}", "%H:%M")
    end_time = datetime.strptime(f"{end//60:02d}:{end%60:02d}", "%H:%M")
    print(f"{day}, {start_time.strftime('%H:%M')} - {end_time.strftime('%H:%M')}")
else:
    print("No available time slot found.")