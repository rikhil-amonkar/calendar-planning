def find_meeting_time(participants_schedules, duration, work_hours, preferences=None):
    """
    Find a meeting time that fits all participants' schedules and constraints.

    Args:
        participants_schedules (dict): A dictionary where keys are participant names and values are lists of busy time slots.
        duration (int): Duration of the meeting in minutes.
        work_hours (tuple): A tuple representing the start and end of work hours in 'HH:MM' format.
        preferences (dict, optional): A dictionary of preferences for each participant. Defaults to None.

    Returns:
        tuple: A tuple containing the day of the week and the meeting time slot in 'HH:MM-HH:MM' format.
    """
    # Convert work hours to minutes since midnight
    work_start = int(work_hours[0].split(':')[0]) * 60 + int(work_hours[0].split(':')[1])
    work_end = int(work_hours[1].split(':')[0]) * 60 + int(work_hours[1].split(':')[1])

    # Initialize a list to keep track of all busy slots
    all_busy_slots = []

    # Process each participant's schedule
    for participant, busy_slots in participants_schedules.items():
        for slot in busy_slots:
            start, end = slot.split(' to ')
            start_min = int(start.split(':')[0]) * 60 + int(start.split(':')[1])
            end_min = int(end.split(':')[0]) * 60 + int(end.split(':')[1])
            all_busy_slots.append((start_min, end_min))

    # Process preferences (Helen's constraint: no meetings after 13:30)
    if preferences:
        for participant, constraint in preferences.items():
            if constraint == "no meetings after 13:30":
                constraint_time = 13 * 60 + 30
                all_busy_slots.append((constraint_time, work_end))

    # Sort all busy slots by start time
    all_busy_slots.sort()

    # Merge overlapping or adjacent busy slots
    merged_slots = []
    for start, end in all_busy_slots:
        if not merged_slots:
            merged_slots.append([start, end])
        else:
            last_start, last_end = merged_slots[-1]
            if start <= last_end:
                merged_slots[-1][1] = max(end, last_end)
            else:
                merged_slots.append([start, end])

    # Find available slots between work hours and busy slots
    available_slots = []
    prev_end = work_start

    for start, end in merged_slots:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that can fit the meeting duration
    for slot in available_slots:
        start, end = slot
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            time_slot = f"{start_hh:02d}:{start_mm:02d}-{end_hh:02d}:{end_mm:02d}"
            return ("Monday", time_slot)

    return (None, None)

# Define participants' schedules
participants_schedules = {
    "Margaret": [
        "9:00 to 10:00",
        "10:30 to 11:00",
        "11:30 to 12:00",
        "13:00 to 13:30",
        "15:00 to 15:30"
    ],
    "Donna": [
        "14:30 to 15:00",
        "16:00 to 16:30"
    ],
    "Helen": [
        "9:00 to 9:30",
        "10:00 to 11:30",
        "13:00 to 14:00",
        "14:30 to 15:00",
        "15:30 to 17:00"
    ]
}

# Define preferences
preferences = {
    "Helen": "no meetings after 13:30"
}

# Define work hours and meeting duration
work_hours = ("9:00", "17:00")
duration = 30  # minutes

# Find the meeting time
day, time_slot = find_meeting_time(participants_schedules, duration, work_hours, preferences)

# Output the result
print(f"{day}: {time_slot}")