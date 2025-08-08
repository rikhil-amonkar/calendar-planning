from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def overlaps(a: Tuple[int, int], b: Tuple[int, int]) -> bool:
    # Intervals are half-open [start, end)
    return not (a[1] <= b[0] or b[1] <= a[0])

def find_meeting_slot(
    work_start: str,
    work_end: str,
    duration_min: int,
    schedules: List[List[Tuple[str, str]]],
) -> Tuple[int, int]:
    ws = to_minutes(work_start)
    we = to_minutes(work_end)

    # Convert all schedules to minutes
    schedules_min = [
        [(to_minutes(s), to_minutes(e)) for s, e in person]
        for person in schedules
    ]

    # Iterate over 30-minute aligned start times within work hours
    for start in range(ws, we - duration_min + 1, 30):
        end = start + duration_min
        candidate = (start, end)

        # Check against all participants' busy intervals
        conflict = False
        for person in schedules_min:
            if any(overlaps(candidate, busy) for busy in person):
                conflict = True
                break

        if not conflict:
            return candidate

    raise ValueError("No available slot found")

if __name__ == "__main__":
    day = "Monday"
    work_start = "09:00"
    work_end = "17:00"
    duration_minutes = 30

    # Busy schedules for Monday
    gregory = [("09:00", "09:30"), ("11:30", "12:00")]
    jonathan = [("09:00", "09:30"), ("12:00", "12:30"), ("13:00", "13:30"), ("15:00", "16:00"), ("16:30", "17:00")]
    barbara = [("10:00", "10:30"), ("13:30", "14:00")]
    jesse = [("10:00", "11:00"), ("12:30", "14:30")]
    alan = [("09:30", "11:00"), ("11:30", "12:30"), ("13:00", "15:30"), ("16:00", "17:00")]
    nicole = [("09:00", "10:30"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "17:00")]
    catherine = [("09:00", "10:30"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]

    schedules = [gregory, jonathan, barbara, jesse, alan, nicole, catherine]

    start_min, end_min = find_meeting_slot(work_start, work_end, duration_minutes, schedules)
    time_range = f"{to_hhmm(start_min)}:{to_hhmm(end_min)}"

    # Output: time range in braces and the day of the week
    print(f"{{{time_range}}}")
    print(day)