from typing import List, Tuple, Dict

# Time utilities
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        ls, le = merged[-1]
        if s <= le:
            merged[-1] = (ls, max(le, e))
        else:
            merged.append((s, e))
    return merged

def invert_within(intervals: List[Interval], window: Interval) -> List[Interval]:
    intervals = merge_intervals([iv for iv in intervals if iv[1] > window[0] and iv[0] < window[1]])
    free = []
    curr = window[0]
    for s, e in intervals:
        if s > curr:
            free.append((curr, s))
        curr = max(curr, e)
    if curr < window[1]:
        free.append((curr, window[1]))
    return free

def intersect_intervals(a: List[Interval], b: List[Interval]) -> List[Interval]:
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

def earliest_slot(slots: List[Interval], duration: int) -> Interval | None:
    for s, e in slots:
        if e - s >= duration:
            return (s, s + duration)
    return None

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    work_window = (work_start, work_end)
    duration = 60  # minutes

    # Busy schedules
    bryan_busy: Dict[str, List[Interval]] = {
        "Monday": [],
        "Tuesday": [],
        "Wednesday": [],
        "Thursday": [(to_minutes("09:30"), to_minutes("10:00")),
                     (to_minutes("12:30"), to_minutes("13:00"))],
        "Friday": [(to_minutes("10:30"), to_minutes("11:00")),
                   (to_minutes("14:00"), to_minutes("14:30"))],
    }

    nicholas_busy: Dict[str, List[Interval]] = {
        "Monday": [(to_minutes("11:30"), to_minutes("12:00")),
                   (to_minutes("13:00"), to_minutes("15:30"))],
        "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                    (to_minutes("11:00"), to_minutes("13:30")),
                    (to_minutes("14:00"), to_minutes("16:30"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:00"), to_minutes("11:00")),
                      (to_minutes("11:30"), to_minutes("13:30")),
                      (to_minutes("14:00"), to_minutes("14:30")),
                      (to_minutes("15:00"), to_minutes("16:30"))],
        "Thursday": [(to_minutes("10:30"), to_minutes("11:30")),
                     (to_minutes("12:00"), to_minutes("12:30")),
                     (to_minutes("15:00"), to_minutes("15:30")),
                     (to_minutes("16:30"), to_minutes("17:00"))],
        "Friday": [(to_minutes("09:00"), to_minutes("10:30")),
                   (to_minutes("11:00"), to_minutes("12:00")),
                   (to_minutes("12:30"), to_minutes("14:30")),
                   (to_minutes("15:30"), to_minutes("16:00")),
                   (to_minutes("16:30"), to_minutes("17:00"))],
    }

    # Preferences (days to avoid if possible)
    avoid = {
        "Bryan": {"Tuesday"},
        "Nicholas": {"Monday", "Thursday"},
    }

    best_choice = None  # (penalty, day_index, start, end, day_name)

    for idx, day in enumerate(days):
        bryan_free = invert_within(bryan_busy.get(day, []), work_window)
        nicholas_free = invert_within(nicholas_busy.get(day, []), work_window)
        common_free = intersect_intervals(bryan_free, nicholas_free)
        slot = earliest_slot(common_free, duration)
        if slot:
            penalty = 0
            penalty += 1 if day in avoid["Bryan"] else 0
            penalty += 1 if day in avoid["Nicholas"] else 0
            s, e = slot
            candidate = (penalty, idx, s, e, day)
            if (best_choice is None) or (candidate < best_choice):
                best_choice = candidate

    if not best_choice:
        raise RuntimeError("No feasible slot found, but the problem statement guarantees a solution.")

    _, _, s, e, day = best_choice
    time_range = f"{to_hhmm(s)}:{to_hhmm(e)}"

    # Output: both the day and the time range (with braces around the time range as an example format)
    print(day)
    print(f"{{{time_range}}}")

if __name__ == "__main__":
    main()