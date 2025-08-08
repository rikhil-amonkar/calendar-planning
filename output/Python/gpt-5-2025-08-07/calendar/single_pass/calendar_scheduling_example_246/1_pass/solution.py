# Meeting scheduler for given participants and constraints
# Outputs the first available 30-minute slot in the format HH:MM:HH:MM and the day of the week

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def overlaps(a_start: int, a_end: int, b_start: int, b_end: int) -> bool:
    return not (a_end <= b_start or a_start >= b_end)

def is_free(busy: List[Tuple[int, int]], start: int, end: int) -> bool:
    return all(not overlaps(start, end, b_start, b_end) for b_start, b_end in busy)

def find_slot(participants_busy: dict, work_start: int, work_end: int, duration: int, step: int = 30) -> Tuple[int, int]:
    for start in range(work_start, work_end - duration + 1, step):
        end = start + duration
        if all(is_free(busy_list, start, end) for busy_list in participants_busy.values()):
            return start, end
    raise ValueError("No available slot found")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    participants_busy_str = {
        "Jacob":  [("13:30", "14:00"), ("14:30", "15:00")],
        "Diana":  [("09:30", "10:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("16:00", "16:30")],
        "Adam":   [("09:30", "10:30"), ("11:00", "12:30"), ("15:30", "16:00")],
        "Angela": [("09:30", "10:00"), ("10:30", "12:00"), ("13:00", "15:30"), ("16:00", "16:30")],
        "Dennis": [("09:00", "09:30"), ("10:30", "11:30"), ("13:00", "15:00"), ("16:30", "17:00")],
    }

    # Convert to minutes
    participants_busy = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in participants_busy_str.items()
    }

    start, end = find_slot(participants_busy, work_start, work_end, duration)
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"

    # Output must include both the time range and the day of the week
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()