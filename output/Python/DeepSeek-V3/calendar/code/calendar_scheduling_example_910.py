from typing import Dict, List, Tuple

def find_meeting_time(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    preferences: Dict[str, List[str]],
    work_hours: Tuple[str, str],
    duration: int,
    days: List[str]
) -> Tuple[str, str]:
    # Convert time string "HH:MM" to minutes since 9:00 (540 minutes)
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes back to "HH:MM" format
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Parse work hours
    work_start, work_end = time_to_minutes(work_hours[0]), time_to_minutes(work_hours[1])
    duration_min = duration * 60

    # Iterate through each day to find a suitable time slot
    for day in days:
        # Skip days based on preferences
        skip_day = False
        for participant, pref_days in preferences.items():
            if day in pref_days:
                skip_day = True
                break
        if skip_day:
            continue

        # Collect all busy intervals for the day
        busy_intervals = []
        for participant, schedule in participants.items():
            if day in schedule:
                for start, end in schedule[day]:
                    busy_start = time_to_minutes(start)
                    busy_end = time_to_minutes(end)
                    busy_intervals.append((busy_start, busy_end))

        # Sort busy intervals by start time
        busy_intervals.sort()

        # Find available slots
        available_slots = []
        prev_end = work_start

        for start, end in busy_intervals:
            if start > prev_end:
                available_slots.append((prev_end, start))
            prev_end = max(prev_end, end)

        if prev_end < work_end:
            available_slots.append((prev_end, work_end))

        # Check for a slot that can fit the meeting
        for slot_start, slot_end in available_slots:
            if slot_end - slot_start >= duration_min:
                meeting_start = slot_start
                meeting_end = meeting_start + duration_min
                return day, f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"

    return None, None

# Define participants' schedules
participants = {
    "Bryan": {
        "Thursday": [("9:30", "10:00"), ("12:30", "13:00")],
        "Friday": [("10:30", "11:00"), ("14:00", "14:30")],
    },
    "Nicholas": {
        "Monday": [("11:30", "12:00"), ("13:00", "15:30")],
        "Tuesday": [("9:00", "9:30"), ("11:00", "13:30"), ("14:00", "16:30")],
        "Wednesday": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
        "Thursday": [("10:30", "11:30"), ("12:00", "12:30"), ("15:00", "15:30"), ("16:30", "17:00")],
        "Friday": [("9:00", "10:30"), ("11:00", "12:00"), ("12:30", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    }
}

# Define preferences
preferences = {
    "Bryan": ["Tuesday"],
    "Nicholas": ["Monday", "Thursday"],
}

# Define other parameters
work_hours = ("9:00", "17:00")
duration = 1  # hour
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Find meeting time
day, time_range = find_meeting_time(participants, preferences, work_hours, duration, days)

# Output the result
print(f"{day}, {time_range}")