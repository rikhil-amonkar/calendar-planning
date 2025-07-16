def find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes):
    # Convert work hours to minutes since midnight for easier calculation
    start_time = work_hours_start * 60
    end_time = work_hours_end * 60
    duration = duration_minutes

    # Initialize a list to keep track of busy intervals for all participants
    busy_intervals = []

    # Collect all busy intervals from each participant's schedule
    for schedule in participants_schedules.values():
        for interval in schedule:
            start_h, start_m = interval[0]
            end_h, end_m = interval[1]
            start = start_h * 60 + start_m
            end = end_h * 60 + end_m
            busy_intervals.append((start, end))

    # Sort all busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                # Overlapping or adjacent, merge them
                new_start = last_start
                new_end = max(last_end, current_end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)

    # Find available slots by checking gaps between merged intervals
    available_slots = []
    previous_end = start_time

    for interval in merged:
        current_start, current_end = interval
        if current_start > previous_end:
            available_slots.append((previous_end, current_start))
        previous_end = max(previous_end, current_end)

    # Check the slot after the last busy interval
    if previous_end < end_time:
        available_slots.append((previous_end, end_time))

    # Find the first available slot that can accommodate the meeting duration
    for slot in available_slots:
        slot_start, slot_end = slot
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            # Convert back to HH:MM format
            start_hh = meeting_start // 60
            start_mm = meeting_start % 60
            end_hh = meeting_end // 60
            end_mm = meeting_end % 60
            return (f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}", day)

    return None

# Define the participants' schedules
participants_schedules = {
    "Gregory": [((9, 0), (9, 30)), ((11, 30), (12, 0))],
    "Jonathan": [((9, 0), (9, 30)), ((12, 0), (12, 30)), ((13, 0), (13, 30)), ((15, 0), (16, 0)), ((16, 30), (17, 0))],
    "Barbara": [((10, 0), (10, 30)), ((13, 30), (14, 0))],
    "Jesse": [((10, 0), (11, 0)), ((12, 30), (14, 30))],
    "Alan": [((9, 30), (11, 0)), ((11, 30), (12, 30)), ((13, 0), (15, 30)), ((16, 0), (17, 0))],
    "Nicole": [((9, 0), (10, 30)), ((11, 30), (12, 0)), ((12, 30), (13, 30)), ((14, 0), (17, 0))],
    "Catherine": [((9, 0), (10, 30)), ((12, 0), (13, 30)), ((15, 0), (15, 30)), ((16, 0), (16, 30))],
}

# Define meeting parameters
day = "Monday"
work_hours_start = 9
work_hours_end = 17
duration_minutes = 30

# Find the meeting time
result = find_meeting_time(participants_schedules, day, work_hours_start, work_hours_end, duration_minutes)

if result:
    time_range, day_of_week = result
    print(f"{time_range} {day_of_week}")
else:
    print("No suitable time found.")