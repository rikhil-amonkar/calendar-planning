from typing import List, Dict, Tuple

def find_meeting_time(
    participants: List[str],
    busy_schedules: Dict[str, List[Tuple[str, str]]],
    preferences: Dict[str, Dict[str, str]],
    meeting_duration: int,
    work_hours: Tuple[str, str],
    day: str
) -> Tuple[str, str]:
    # Convert all time strings to minutes since 9:00 (start of work hours)
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm - 9 * 60  # Offset by 9:00 (540 minutes)

    def minutes_to_time(minutes: int) -> str:
        total_minutes = 9 * 60 + minutes
        hh = total_minutes // 60
        mm = total_minutes % 60
        return f"{hh:02d}:{mm:02d}"

    start_work, end_work = work_hours
    work_start = time_to_minutes(start_work)
    work_end = time_to_minutes(end_work)

    # Initialize all available slots as free
    free_slots = [True] * (work_end - work_start)

    # Mark busy slots for each participant
    for participant in participants:
        for busy_start, busy_end in busy_schedules.get(participant, []):
            busy_start_min = time_to_minutes(busy_start)
            busy_end_min = time_to_minutes(busy_end)
            for i in range(busy_start_min, busy_end_min):
                if 0 <= i < len(free_slots):
                    free_slots[i] = False

    # Apply preferences (Janice prefers before 13:00)
    if "Janice" in preferences and "preferred_time" in preferences["Janice"]:
        pref_time = preferences["Janice"]["preferred_time"]
        pref_cutoff = time_to_minutes(pref_time)
        for i in range(pref_cutoff, len(free_slots)):
            free_slots[i] = False

    # Find the earliest slot that fits the meeting duration
    required_slots = meeting_duration
    current_slot_start = -1
    consecutive_free = 0

    for i in range(len(free_slots)):
        if free_slots[i]:
            if consecutive_free == 0:
                current_slot_start = i
            consecutive_free += 1
            if consecutive_free >= required_slots:
                start_time = minutes_to_time(current_slot_start)
                end_time = minutes_to_time(current_slot_start + required_slots)
                return (start_time, end_time)
        else:
            consecutive_free = 0

    return None

# Define the problem
participants = ["Christine", "Janice", "Bobby", "Elizabeth", "Tyler", "Edward"]
busy_schedules = {
    "Christine": [("9:30", "10:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "16:30")],
    "Bobby": [("12:00", "12:30"), ("14:30", "15:00")],
    "Elizabeth": [("9:00", "9:30"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "17:00")],
    "Tyler": [("9:00", "11:00"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:30", "16:00"), ("16:30", "17:00")],
    "Edward": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
}
preferences = {
    "Janice": {"preferred_time": "13:00"},
}
meeting_duration = 30  # minutes
work_hours = ("9:00", "17:00")
day = "Monday"

# Find the meeting time
start_time, end_time = find_meeting_time(participants, busy_schedules, preferences, meeting_duration, work_hours, day)

# Output the result
print(f"{day}: {start_time}:{end_time}")