# Meeting scheduler for Carl and Margaret
# Finds a 60-minute slot between 09:00 and 17:00, Monday-Thursday,
# preferring non-Thursday days (to honor Carl's preference).

from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def subtract_intervals(base: List[Tuple[int, int]], sub: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Subtract list 'sub' from list 'base' (both non-overlapping, sorted)
    result = []
    i, j = 0, 0
    while i < len(base):
        bs, be = base[i]
        cur_start = bs
        while j < len(sub) and sub[j][1] <= bs:
            j += 1
        k = j
        while k < len(sub) and sub[k][0] < be:
            ss, se = sub[k]
            if ss > cur_start:
                result.append((cur_start, min(ss, be)))
            cur_start = max(cur_start, se)
            if cur_start >= be:
                break
            k += 1
        if cur_start < be:
            result.append((cur_start, be))
        i += 1
    return [(s, e) for s, e in result if e > s]

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i, j = 0, 0
    out = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            out.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return out

WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
MEETING_DURATION = 60

days_order = ["Monday", "Tuesday", "Wednesday", "Thursday"]  # Prefer earlier days; Thursday last

schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Carl": {
        "Monday": [(to_minutes("11:00"), to_minutes("11:30"))],
        "Tuesday": [(to_minutes("14:30"), to_minutes("15:00"))],
        "Wednesday": [(to_minutes("10:00"), to_minutes("11:30")), (to_minutes("13:00"), to_minutes("13:30"))],
        "Thursday": [(to_minutes("13:30"), to_minutes("14:00")), (to_minutes("16:00"), to_minutes("16:30"))],
    },
    "Margaret": {
        "Monday": [(to_minutes("09:00"), to_minutes("10:30")), (to_minutes("11:00"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:30"), to_minutes("12:00")), (to_minutes("13:30"), to_minutes("14:00")), (to_minutes("15:30"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:30"), to_minutes("12:00")), (to_minutes("12:30"), to_minutes("13:00")),
                      (to_minutes("13:30"), to_minutes("14:30")), (to_minutes("15:00"), to_minutes("17:00"))],
        "Thursday": [(to_minutes("10:00"), to_minutes("12:00")), (to_minutes("12:30"), to_minutes("14:00")), (to_minutes("14:30"), to_minutes("17:00"))],
    },
}

def day_free_intervals(person: str, day: str) -> List[Tuple[int, int]]:
    work_block = [(WORK_START, WORK_END)]
    busy = schedules.get(person, {}).get(day, [])
    # Clip busy intervals to work hours and merge
    clipped = []
    for s, e in busy:
        s = max(s, WORK_START)
        e = min(e, WORK_END)
        if s < e:
            clipped.append((s, e))
    busy_merged = merge_intervals(clipped)
    return subtract_intervals(work_block, busy_merged)

def find_meeting() -> Tuple[str, int, int]:
    for day in days_order:
        # Compute intersection of all participants' free intervals for this day
        participants = list(schedules.keys())
        joint_free = day_free_intervals(participants[0], day)
        for p in participants[1:]:
            joint_free = intersect_intervals(joint_free, day_free_intervals(p, day))
            if not joint_free:
                break
        if not joint_free:
            continue
        # Find earliest slot of required duration
        for s, e in joint_free:
            if e - s >= MEETING_DURATION:
                start = s
                end = s + MEETING_DURATION
                return day, start, end
    raise ValueError("No feasible meeting slot found")

if __name__ == "__main__":
    day, start, end = find_meeting()
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")