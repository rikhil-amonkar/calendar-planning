# Meeting Scheduler for John and Jennifer
# Goal: Find a 30-minute meeting within 09:00-17:00 on Mon/Tue/Wed,
# respecting schedules and John's preferences:
# - Prefer Monday before 14:30
# - Avoid Monday after 14:30 if possible
# - Avoid Tuesday and Wednesday if possible

from typing import List, Tuple, Dict

TimeInterval = Tuple[int, int]  # minutes since midnight

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def free_from_busy(work: TimeInterval, busy: List[TimeInterval]) -> List[TimeInterval]:
    ws, we = work
    busy_sorted = sorted(busy)
    free = []
    cur = ws
    for bs, be in busy_sorted:
        if be <= ws or bs >= we:
            continue
        bs, be = max(bs, ws), min(be, we)
        if bs > cur:
            free.append((cur, bs))
        cur = max(cur, be)
    if cur < we:
        free.append((cur, we))
    return free

def intersect(a: List[TimeInterval], b: List[TimeInterval]) -> List[TimeInterval]:
    i, j = 0, 0
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

def score_slot(day: str, start: int, end: int) -> Tuple[int, int]:
    # Lower is better. Primary by preference, then earlier time.
    monday_cutoff = to_minutes("14:30")
    if day == "Monday":
        if end <= monday_cutoff:
            pref = 0  # best: Monday before or ending by 14:30
        else:
            pref = 1  # Monday after 14:30
    else:
        pref = 2  # Tuesday/Wednesday (avoid if possible)
    return (pref, start)

def pick_slot(common_free: List[TimeInterval], duration: int, day: str) -> Tuple[int, int]:
    best = None
    for s, e in common_free:
        if e - s >= duration:
            start = s
            end = s + duration
            cand = (start, end)
            sc = score_slot(day, start, end)
            if best is None or sc < best[0]:
                best = (sc, cand)
    return best[1] if best else None

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    work_hours = (to_minutes("09:00"), to_minutes("17:00"))
    duration = 30  # minutes

    # Schedules (busy intervals)
    jennifer_busy: Dict[str, List[TimeInterval]] = {
        "Monday":   [(to_minutes("09:00"), to_minutes("11:00")),
                     (to_minutes("11:30"), to_minutes("13:00")),
                     (to_minutes("13:30"), to_minutes("14:30")),
                     (to_minutes("15:00"), to_minutes("17:00"))],
        "Tuesday":  [(to_minutes("09:00"), to_minutes("11:30")),
                     (to_minutes("12:00"), to_minutes("17:00"))],
        "Wednesday":[(to_minutes("09:00"), to_minutes("11:30")),
                     (to_minutes("12:00"), to_minutes("12:30")),
                     (to_minutes("13:00"), to_minutes("14:00")),
                     (to_minutes("14:30"), to_minutes("16:00")),
                     (to_minutes("16:30"), to_minutes("17:00"))],
    }
    john_busy: Dict[str, List[TimeInterval]] = {d: [] for d in days}  # John has no meetings

    # Compute candidate across days, honoring preferences via scoring
    chosen = None  # (score_tuple, (day, start, end))
    for day in days:
        john_free = free_from_busy(work_hours, john_busy.get(day, []))
        jennifer_free = free_from_busy(work_hours, jennifer_busy.get(day, []))
        common = intersect(john_free, jennifer_free)
        slot = pick_slot(common, duration, day)
        if slot:
            s, e = slot
            sc = score_slot(day, s, e)
            if chosen is None or sc < chosen[0]:
                chosen = (sc, (day, s, e))

    if not chosen:
        raise RuntimeError("No feasible slot found, but a solution was expected.")

    day, s, e = chosen[1]
    print(f"{day} {{{to_hhmm(s)}:{to_hhmm(e)}}}")

if __name__ == "__main__":
    main()