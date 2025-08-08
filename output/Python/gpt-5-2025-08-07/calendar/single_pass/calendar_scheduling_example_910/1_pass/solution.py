from typing import List, Tuple, Dict

def time_to_min(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(x: int) -> str:
    return f"{x // 60:02d}:{x % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def invert_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(work_start, work_end)]
    # Clip busy to work hours and merge
    clipped = []
    for s, e in busy:
        if e <= work_start or s >= work_end:
            continue
        clipped.append((max(s, work_start), min(e, work_end)))
    merged = merge_intervals(clipped)
    free = []
    cur = work_start
    for s, e in merged:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
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

def schedule_meeting() -> Tuple[str, str, str]:
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_index = {d: i for i, d in enumerate(days)}
    work_start = time_to_min("09:00")
    work_end = time_to_min("17:00")
    duration = 60  # minutes

    # Schedules (start, end) in HH:MM within 09:00-17:00 window
    bryan_sched_raw: Dict[str, List[Tuple[str, str]]] = {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
        "Thursday": [("09:30", "10:00"), ("12:30", "13:00")],
        "Friday": [("10:30", "11:00"), ("14:00", "14:30")],
    }
    nicholas_sched_raw: Dict[str, List[Tuple[str, str]]] = {
        "Monday": [("11:30", "12:00"), ("13:00", "15:30")],
        "Tuesday": [("09:00", "09:30"), ("11:00", "13:30"), ("14:00", "16:30")],
        "Wednesday": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "13:30"),
                      ("14:00", "14:30"), ("15:00", "16:30")],
        "Thursday": [("10:30", "11:30"), ("12:00", "12:30"), ("15:00", "15:30"), ("16:30", "17:00")],
        "Friday": [("09:00", "10:30"), ("11:00", "12:00"), ("12:30", "14:30"),
                   ("15:30", "16:00"), ("16:30", "17:00")],
    }

    # Preferences (soft constraints)
    bryan_avoid = {"Tuesday"}
    nicholas_avoid = {"Monday", "Thursday"}  # "Monday. Thursday." interpreted as both Monday and Thursday

    # Convert to minute-based schedules
    def to_minutes(sched_raw: Dict[str, List[Tuple[str, str]]]) -> Dict[str, List[Tuple[int, int]]]:
        out = {}
        for d in days:
            out[d] = [(time_to_min(s), time_to_min(e)) for s, e in sched_raw.get(d, [])]
        return out

    bryan_sched = to_minutes(bryan_sched_raw)
    nicholas_sched = to_minutes(nicholas_sched_raw)

    candidates = []  # (penalty, day_index, start_min, end_min, day)
    for d in days:
        b_busy = bryan_sched.get(d, [])
        n_busy = nicholas_sched.get(d, [])
        b_free = invert_to_free(b_busy, work_start, work_end)
        n_free = invert_to_free(n_busy, work_start, work_end)
        overlap = intersect_intervals(b_free, n_free)
        for s, e in overlap:
            if e - s >= duration:
                start = s
                end = s + duration
                penalty = (1 if d in bryan_avoid else 0) + (1 if d in nicholas_avoid else 0)
                candidates.append((penalty, day_index[d], start, end, d))

    if not candidates:
        raise RuntimeError("No feasible meeting slot found.")

    candidates.sort()
    _, _, best_start, best_end, best_day = candidates[0]
    time_range = f"{min_to_time(best_start)}:{min_to_time(best_end)}"

    # Output must include the time range in {HH:MM:HH:MM} and the day of the week
    print(f"{best_day} {{{time_range}}}")

if __name__ == "__main__":
    schedule_meeting()