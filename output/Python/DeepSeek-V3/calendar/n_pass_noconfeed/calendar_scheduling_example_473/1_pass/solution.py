from typing import List, Dict, Tuple

def find_meeting_time(
    participants: Dict[str, List[Tuple[str, str]]],
    duration_minutes: int,
    work_hours_start: str,
    work_hours_end: str,
    day: str
) -> Tuple[str, str]:
    # Convert time string "HH:MM" to minutes since midnight
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    # Convert minutes since midnight to "HH:MM" string
    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    # Parse work hours
    work_start = time_to_minutes(work_hours_start)
    work_end = time_to_minutes(work_hours_end)

    # Collect all busy intervals for all participants
    busy_intervals = []
    for person, intervals in participants.items():
        for start, end in intervals:
            busy_intervals.append((time_to_minutes(start), time_to_minutes(end)))
    
    # Sort intervals by start time
    busy_intervals.sort()

    # Merge overlapping or adjacent intervals
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

    # Find available slots
    available_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find first slot that fits the duration
    duration = duration_minutes
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
    participants = {
        "Gregory": [("9:00", "9:30"), ("11:30", "12:00")],
        "Jonathan": [("9:00", "9:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        "Barbara": [("10:00", "10:30"), ("13:30", "14:00")],
        "Jesse": [("10:00", "11:00"), ("12:30", "14:30")],
        "Alan": [("9:30", "11:00"), ("11:30", "12:30"), ("13:00", "15:30"), ("16:00", "17:00")],
        "Nicole": [("9:00", "10:30"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "17:00")],
        "Catherine": [("9:00", "10:30"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")],
    }

    duration_minutes = 30
    work_hours_start = "9:00"
    work_hours_end = "17:00"
    day = "Monday"

    start_time, end_time = find_meeting_time(
        participants, duration_minutes, work_hours_start, work_hours_end, day
    )

    if start_time and end_time:
        print(f"{day}: {start_time}:{end_time}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()