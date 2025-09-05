from typing import List, Tuple, Dict

# Meeting configuration
MEETING_DURATION_MIN = 30  # minutes
WORK_HOURS = {
    "Monday":  (9*60, 17*60),
    "Tuesday": (9*60, 17*60),
}

# Existing schedules (busy times) in minutes since midnight
schedules: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Shirley": {
        "Monday":  [(10*60+30, 11*60), (12*60, 12*60+30), (16*60, 16*60+30)],
        "Tuesday": [(9*60+30, 10*60)],
    },
    "Albert": {
        "Monday":  [(9*60, 17*60)],
        "Tuesday": [(9*60+30, 11*60), (11*60+30, 12*60+30), (13*60, 16*60), (16*60+30, 17*60)],
    }
}

# Preferences: avoid Tuesday after 10:30 for Shirley
PREFERENCES = {
    "Tuesday": {"avoid_after": 10*60 + 30}  # prefer start times at or before 10:30 on Tuesday
}

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def invert_intervals(busy: List[Tuple[int, int]], bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start_bound, end_bound = bounds
    busy = [(max(start_bound, s), min(end_bound, e)) for s, e in busy]
    busy = [(s, e) for s, e in busy if s < e]
    busy = merge_intervals(busy)

    free = []
    cursor = start_bound
    for s, e in busy:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end_bound:
        free.append((cursor, end_bound))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    out = []
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    result = lists[0]
    for nxt in lists[1:]:
        result = intersect_two(result, nxt)
        if not result:
            break
    return result

def slots_of_length(intervals: List[Tuple[int, int]], length: int) -> List[Tuple[int, int]]:
    slots = []
    for s, e in intervals:
        t = s
        while t + length <= e:
            slots.append((t, t + length))
            # Step at 1-minute granularity
            t += 1
    return slots

def fmt_time(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def pick_slot() -> Tuple[str, Tuple[int, int]]:
    days_order = ["Monday", "Tuesday"]

    for day in days_order:
        bounds = WORK_HOURS[day]
        # Compute free intervals for each participant
        free_lists = []
        for person in schedules:
            busy = schedules[person].get(day, [])
            free_lists.append(invert_intervals(busy, bounds))

        # Intersect free intervals across participants
        common_free = intersect_all(free_lists)
        if not common_free:
            continue

        # Generate all candidate slots of the required length
        candidates = slots_of_length(common_free, MEETING_DURATION_MIN)

        if not candidates:
            continue

        # Apply preferences: first try preferred slots, then any
        preferred = candidates
        if day in PREFERENCES and "avoid_after" in PREFERENCES[day]:
            cutoff = PREFERENCES[day]["avoid_after"]
            preferred = [slot for slot in candidates if slot[0] <= cutoff]

        if preferred:
            return day, min(preferred, key=lambda x: x[0])

        # If no preferred slot, fall back to any candidate that day
        return day, min(candidates, key=lambda x: x[0])

    raise RuntimeError("No feasible slot found")

if __name__ == "__main__":
    day, (start, end) = pick_slot()
    # Output includes both the time range and the day of the week
    print(f"{day} {{{fmt_time(start)}:{fmt_time(end)}}}")