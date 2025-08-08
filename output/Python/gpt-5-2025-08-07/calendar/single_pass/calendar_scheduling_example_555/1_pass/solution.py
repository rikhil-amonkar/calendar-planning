from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

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

def complement_intervals(busy: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    busy = merge_intervals([(max(ws, s), min(we, e)) for s, e in busy if e > ws and s < we])
    free = []
    cur = ws
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            res.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return res

def first_slot_of_duration(free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free:
        if e - s >= duration:
            return (s, s + duration)
    raise ValueError("No suitable slot found")

def main():
    # Configuration
    day = "Monday"
    meeting_duration_min = 30
    work_start, work_end = parse_time("09:00"), parse_time("17:00")

    # Participants' schedules and preferences
    # Evelyn: no meetings, but prefers not to meet after 13:00 on Monday
    evelyn_pref_end = parse_time("13:00")
    evelyn_busy = []  # no meetings
    evelyn_window = (work_start, min(work_end, evelyn_pref_end))

    # Randy's busy times on Monday
    randy_busy_str = [("09:00", "10:30"), ("11:00", "15:30"), ("16:00", "17:00")]
    randy_busy = [(parse_time(s), parse_time(e)) for s, e in randy_busy_str]
    randy_window = (work_start, work_end)

    # Compute free intervals
    evelyn_free = complement_intervals(evelyn_busy, evelyn_window)
    randy_free = complement_intervals(randy_busy, randy_window)

    # Find mutual free intervals
    mutual_free = intersect_intervals(evelyn_free, randy_free)

    # Select the earliest slot of required duration
    start, end = first_slot_of_duration(mutual_free, meeting_duration_min)

    # Output
    print(f"{fmt_time(start)}:{fmt_time(end)}")
    print(day)

if __name__ == "__main__":
    main()