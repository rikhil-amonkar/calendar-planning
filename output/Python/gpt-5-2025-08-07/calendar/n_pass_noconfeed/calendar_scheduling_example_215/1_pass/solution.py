# Meeting Scheduler for Monday between 09:00 and 17:00
# Participants: Steven, Roy, Cynthia, Lauren, Robert
# Goal: Find the earliest 30-minute slot that works for everyone

from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def clamp_interval(interval: Tuple[int, int], lo: int, hi: int) -> Tuple[int, int]:
    s, e = interval
    s = max(s, lo)
    e = min(e, hi)
    return (s, e) if s < e else None

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals.sort()
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def find_earliest_slot(busy_all: List[Tuple[int, int]], work_start: int, work_end: int, duration: int) -> Tuple[int, int]:
    merged = merge_intervals(busy_all)
    candidate = work_start
    for s, e in merged:
        if candidate + duration <= s:
            return candidate, candidate + duration
        candidate = max(candidate, e)
    if candidate + duration <= work_end:
        return candidate, candidate + duration
    return None

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    busy = {
        "Steven": [],
        "Roy": [],
        "Cynthia": [("09:30", "10:30"), ("11:30", "12:00"), ("13:00", "13:30"), ("15:00", "16:00")],
        "Lauren": [("09:00", "09:30"), ("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"),
                   ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")],
        "Robert": [("10:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "16:00")],
    }

    # Gather all busy intervals across participants, clamped to work hours
    busy_all: List[Tuple[int, int]] = []
    for intervals in busy.values():
        for s_str, e_str in intervals:
            s, e = to_minutes(s_str), to_minutes(e_str)
            clamped = clamp_interval((s, e), work_start, work_end)
            if clamped:
                busy_all.append(clamped)

    slot = find_earliest_slot(busy_all, work_start, work_end, duration)
    if not slot:
        raise RuntimeError("No available slot found, despite problem statement guaranteeing one.")
    start, end = slot
    start_str, end_str = to_hhmm(start), to_hhmm(end)

    # Output must include time range in braces and the day of the week
    print(f"{day} {{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()