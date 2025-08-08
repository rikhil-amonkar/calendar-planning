from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
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

def clamp_interval(interval: Interval, bounds: Interval) -> Interval | None:
    s, e = interval
    bs, be = bounds
    s = max(s, bs)
    e = min(e, be)
    if s >= e:
        return None
    return (s, e)

def subtract_busy_from_window(window: Interval, busy: List[Interval]) -> List[Interval]:
    # Assumes window is a single interval; busy may be many intervals.
    bs, be = window
    busy = [i for i in (clamp_interval(b, window) for b in busy) if i]
    busy = merge_intervals(busy)
    free: List[Interval] = []
    cursor = bs
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < be:
        free.append((cursor, be))
    return free

def intersect_interval_lists(a: List[Interval], b: List[Interval]) -> List[Interval]:
    i = j = 0
    out: List[Interval] = []
    while i < len(a) and j < len(b):
        s1, e1 = a[i]
        s2, e2 = b[j]
        s = max(s1, s2)
        e = min(e1, e2)
        if s < e:
            out.append((s, e))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return out

def first_slot(intervals: List[Interval], duration: int) -> Interval | None:
    for s, e in intervals:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    # Meeting parameters
    duration_minutes = 30
    days = ["Monday", "Tuesday"]
    work_window: Dict[str, Interval] = {
        "Monday": (to_minutes("09:00"), to_minutes("17:00")),
        "Tuesday": (to_minutes("09:00"), to_minutes("17:00")),
    }

    # Participants' busy schedules
    jesse_busy_raw: Dict[str, List[Tuple[str, str]]] = {
        "Monday": [("13:30", "14:00"), ("14:30", "15:00")],
        "Tuesday": [("09:00", "09:30"), ("13:00", "13:30"), ("14:00", "15:00")],
    }
    lawrence_busy_raw: Dict[str, List[Tuple[str, str]]] = {
        "Monday": [("09:00", "17:00")],
        "Tuesday": [("09:30", "10:30"), ("11:30", "12:30"), ("13:00", "13:30"),
                    ("14:30", "15:00"), ("15:30", "16:30")],
    }

    # Convert to minutes
    jesse_busy = {
        d: [(to_minutes(s), to_minutes(e)) for s, e in jesse_busy_raw.get(d, [])]
        for d in days
    }
    lawrence_busy = {
        d: [(to_minutes(s), to_minutes(e)) for s, e in lawrence_busy_raw.get(d, [])]
        for d in days
    }

    # Apply additional constraint: Lawrence cannot meet on Tuesday after 16:30
    lawrence_day_window = dict(work_window)
    lawrence_day_window["Tuesday"] = (
        lawrence_day_window["Tuesday"][0],
        min(lawrence_day_window["Tuesday"][1], to_minutes("16:30")),
    )

    # Find the first feasible slot across the allowed days
    for day in days:
        # Jesse availability within work hours
        jesse_free = subtract_busy_from_window(work_window[day], jesse_busy.get(day, []))
        # Lawrence availability within constrained window
        lawrence_free = subtract_busy_from_window(lawrence_day_window[day], lawrence_busy.get(day, []))
        # Mutual availability
        mutual = intersect_interval_lists(jesse_free, lawrence_free)
        slot = first_slot(mutual, duration_minutes)
        if slot:
            start, end = slot
            print(f"{day} {{{to_time(start)}:{to_time(end)}}}")
            return

if __name__ == "__main__":
    main()