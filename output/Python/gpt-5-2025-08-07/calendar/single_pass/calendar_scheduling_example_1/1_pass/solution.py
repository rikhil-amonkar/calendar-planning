from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def normalize_busy(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    # Clip to work hours and merge overlaps
    clipped = []
    for s, e in sorted(busy):
        s = max(s, ws)
        e = min(e, we)
        if s >= e:
            continue
        if not clipped or s > clipped[-1][1]:
            clipped.append([s, e])
        else:
            clipped[-1][1] = max(clipped[-1][1], e)
    return [(s, e) for s, e in clipped]

def free_from_busy(busy: List[Tuple[int, int]], ws: int, we: int) -> List[Tuple[int, int]]:
    free = []
    cur = ws
    for s, e in busy:
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < we:
        free.append((cur, we))
    return free

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

def find_meeting_slot(participants_busy: List[List[Tuple[int, int]]],
                      ws: int, we: int, duration: int,
                      preference_before: int = None) -> Tuple[int, int]:
    # Convert busy to free for each participant
    frees = []
    for busy in participants_busy:
        nb = normalize_busy(busy, ws, we)
        fr = free_from_busy(nb, ws, we)
        frees.append(fr)

    # Intersect all free intervals
    common = frees[0]
    for fr in frees[1:]:
        common = intersect_intervals(common, fr)

    # Generate candidate slots (start at interval start)
    candidates = []
    for s, e in common:
        if e - s >= duration:
            candidates.append((s, s + duration))

    if not candidates:
        raise ValueError("No available slot found")

    # Apply preference: choose earliest slot starting before the preference time if possible
    if preference_before is not None:
        preferred = [c for c in candidates if c[0] < preference_before]
        if preferred:
            return min(preferred, key=lambda x: x[0])

    # Otherwise choose earliest overall
    return min(candidates, key=lambda x: x[0])

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    # Existing schedules
    raymond_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("11:30"), to_minutes("12:00")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
    ]
    billy_busy = [
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("16:30"), to_minutes("17:00")),
    ]
    donald_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("10:00"), to_minutes("11:00")),
        (to_minutes("12:00"), to_minutes("13:00")),
        (to_minutes("14:00"), to_minutes("14:30")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]

    # Billy would like to avoid meetings after 15:00 on Monday
    preference_before = to_minutes("15:00")

    start, end = find_meeting_slot(
        [raymond_busy, billy_busy, donald_busy],
        work_start, work_end, duration,
        preference_before=preference_before
    )

    print(f"{to_hhmm(start)}:{to_hhmm(end)}")
    print(day)

if __name__ == "__main__":
    main()