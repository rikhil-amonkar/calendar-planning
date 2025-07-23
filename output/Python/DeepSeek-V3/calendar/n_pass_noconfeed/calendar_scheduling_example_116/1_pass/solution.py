from typing import List, Dict, Tuple

def find_meeting_time(
    participants: List[str],
    schedules: Dict[str, List[Tuple[str, str]]],
    preferences: Dict[str, List[Tuple[str, str]]],
    duration: int,
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

    # Parse work hours
    work_start = time_to_minutes(work_hours[0])
    work_end = time_to_minutes(work_hours[1])

    # Collect all busy intervals for all participants
    busy_intervals = []
    for participant in participants:
        for start, end in schedules.get(participant, []):
            busy_start = time_to_minutes(start)
            busy_end = time_to_minutes(end)
            busy_intervals.append((busy_start, busy_end))

    # Add preference constraints as busy intervals
    for participant, pref_intervals in preferences.items():
        for start, end in pref_intervals:
            pref_start = time_to_minutes(start)
            pref_end = time_to_minutes(end)
            # Treat "rather not meet before X" as busy before X
            if pref_start == 0 and pref_end > 0:
                busy_intervals.append((work_start, pref_end))
            else:
                # Generic case (not used in this example)
                busy_intervals.append((pref_start, pref_end))

    # Sort busy intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in busy_intervals:
        if not merged:
            merged.append([start, end])
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                merged[-1][1] = max(end, last_end)
            else:
                merged.append([start, end])

    # Find available slots (gaps between busy intervals)
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that can fit the duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration:
            meeting_start = slot_start
            meeting_end = meeting_start + duration
            return (
                minutes_to_time(meeting_start),
                minutes_to_time(meeting_end)
            )

    return None, None

def main():
    participants = ["Adam", "John", "Stephanie", "Anna"]
    schedules = {
        "Adam": [("14:00", "15:00")],
        "John": [
            ("13:00", "13:30"),
            ("14:00", "14:30"),
            ("15:30", "16:00"),
            ("16:30", "17:00")
        ],
        "Stephanie": [
            ("9:30", "10:00"),
            ("10:30", "11:00"),
            ("11:30", "16:00"),
            ("16:30", "17:00")
        ],
        "Anna": [
            ("9:30", "10:00"),
            ("12:00", "12:30"),
            ("13:00", "15:30"),
            ("16:30", "17:00")
        ]
    }
    preferences = {
        "Anna": [("00:00", "14:30")]  # Rather not meet before 14:30
    }
    duration = 30  # minutes
    work_hours = ("9:00", "17:00")
    day = "Monday"

    start_time, end_time = find_meeting_time(
        participants, schedules, preferences, duration, work_hours, day
    )

    if start_time and end_time:
        print(f"{day}:{start_time}:{end_time}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()