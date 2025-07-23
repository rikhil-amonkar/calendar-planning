from typing import List, Dict, Tuple

def find_meeting_time(participants: Dict[str, List[Tuple[str, str]]], duration: int, work_hours: Tuple[str, str]) -> Tuple[str, str]:
    # Convert all time slots to minutes since midnight for easier comparison
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    work_start, work_end = map(time_to_minutes, work_hours)
    duration_min = duration

    # Generate all busy intervals across all participants
    all_busy = []
    for person, slots in participants.items():
        for start, end in slots:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            all_busy.append((start_min, end_min))

    # Sort all busy intervals by start time
    all_busy.sort()

    # Merge overlapping or adjacent busy intervals
    merged = []
    for start, end in all_busy:
        if not merged:
            merged.append((start, end))
        else:
            last_start, last_end = merged[-1]
            if start <= last_end:
                new_start = min(last_start, start)
                new_end = max(last_end, end)
                merged[-1] = (new_start, new_end)
            else:
                merged.append((start, end))

    # Find all available time slots
    available_slots = []
    prev_end = work_start

    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)

    if prev_end < work_end:
        available_slots.append((prev_end, work_end))

    # Find the first available slot that fits the duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_min:
            return slot_start, slot_start + duration_min

    return None, None

def minutes_to_time(minutes: int) -> str:
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

def main():
    participants = {
        "Andrea": [("09:30", "10:30"), ("13:30", "14:30")],
        "Ruth": [("12:30", "13:00"), ("15:00", "15:30")],
        "Steven": [("10:00", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"), ("13:30", "14:00"), ("15:00", "16:00")],
        "Grace": [],
        "Kyle": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "13:00"), ("13:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Elijah": [("09:00", "11:00"), ("11:30", "13:00"), ("13:30", "14:00"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Lori": [("09:00", "09:30"), ("10:00", "11:30"), ("12:00", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
    }

    duration = 30  # minutes
    work_hours = ("09:00", "17:00")
    day = "Monday"

    start_min, end_min = find_meeting_time(participants, duration, work_hours)

    if start_min is not None and end_min is not None:
        start_time = minutes_to_time(start_min)
        end_time = minutes_to_time(end_min)
        print(f"{day}: {start_time}-{end_time}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()