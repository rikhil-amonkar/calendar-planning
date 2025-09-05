from typing import List, Tuple, Optional

# Meeting configuration
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_DURATION_MIN = 30

# Participants' busy schedules
robert_busy = {
    "Monday":    [("11:00", "11:30"), ("14:00", "14:30"), ("15:30", "16:00")],
    "Tuesday":   [("10:30", "11:00"), ("15:00", "15:30")],
    "Wednesday": [("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:00"),
                  ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
}

ralph_busy = {
    "Monday":    [("10:00", "13:30"), ("14:00", "14:30"), ("15:00", "17:00")],
    "Tuesday":   [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"),
                  ("12:00", "13:00"), ("14:00", "15:30"), ("16:00", "17:00")],
    "Wednesday": [("10:30", "11:00"), ("11:30", "12:00"), ("13:00", "14:30"),
                  ("16:30", "17:00")],
}

# Constraints
allowed_days = ["Monday", "Tuesday", "Wednesday"]
# Preference: avoid Monday if possible -> prioritize Tue, Wed, then Mon
search_order = ["Tuesday", "Wednesday", "Monday"]


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


def invert_intervals(busy: List[Tuple[int, int]], start: int, end: int) -> List[Tuple[int, int]]:
    # Given busy intervals within [start, end], return free intervals
    free = []
    cursor = start
    for s, e in busy:
        if s > cursor:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < end:
        free.append((cursor, end))
    return free


def intersect_earliest_slot(free_a: List[Tuple[int, int]],
                            free_b: List[Tuple[int, int]],
                            duration: int) -> Optional[Tuple[int, int]]:
    i = j = 0
    while i < len(free_a) and j < len(free_b):
        s = max(free_a[i][0], free_b[j][0])
        e = min(free_a[i][1], free_b[j][1])
        if e - s >= duration:
            return (s, s + duration)
        if free_a[i][1] < free_b[j][1]:
            i += 1
        else:
            j += 1
    return None


def earliest_meeting_day(day: str) -> Optional[Tuple[int, int, str]]:
    ws, we = to_minutes(WORK_START), to_minutes(WORK_END)
    # Build busy intervals for both participants for the given day
    ra = merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in robert_busy.get(day, [])])
    rb = merge_intervals([(to_minutes(s), to_minutes(e)) for s, e in ralph_busy.get(day, [])])

    # Clip busy intervals to work hours
    ra = [(max(ws, s), min(we, e)) for s, e in ra if min(we, e) > max(ws, s)]
    rb = [(max(ws, s), min(we, e)) for s, e in rb if min(we, e) > max(ws, s)]

    # Compute free intervals within work hours
    free_r = invert_intervals(ra, ws, we)
    free_l = invert_intervals(rb, ws, we)

    slot = intersect_earliest_slot(free_r, free_l, MEETING_DURATION_MIN)
    if slot:
        return slot[0], slot[1], day
    return None


def find_meeting() -> Tuple[str, str]:
    # Try preferred order (avoid Monday)
    for day in search_order:
        if day not in allowed_days:
            continue
        res = earliest_meeting_day(day)
        if res:
            start_min, end_min, d = res
            return d, f"{to_hhmm(start_min)}:{to_hhmm(end_min)}"
    # Fallback to any allowed day (shouldn't be needed per problem statement)
    for day in allowed_days:
        res = earliest_meeting_day(day)
        if res:
            start_min, end_min, d = res
            return d, f"{to_hhmm(start_min)}:{to_hhmm(end_min)}"
    raise RuntimeError("No feasible meeting time found.")


if __name__ == "__main__":
    day, time_range = find_meeting()
    print(f"{day} {{{time_range}}}")