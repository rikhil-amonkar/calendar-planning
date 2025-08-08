from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

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

def complement_within(day_span: Tuple[int, int], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = day_span
    busy = merge_intervals([(max(start, s), min(end, e)) for s, e in busy if e > start and s < end])
    if not busy:
        return [(start, end)]
    free = []
    cur = start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < end:
        free.append((cur, end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
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

def clip_intervals(intervals: List[Tuple[int, int]], clip_span: Tuple[int, int]) -> List[Tuple[int, int]]:
    cs, ce = clip_span
    clipped = []
    for s, e in intervals:
        ns, ne = max(s, cs), min(e, ce)
        if ns < ne:
            clipped.append((ns, ne))
    return clipped

# Input data
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes
days = ["Monday", "Tuesday", "Wednesday"]

schedule: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Joshua": {
        "Monday":   [("15:00", "15:30")],
        "Tuesday":  [("11:30", "12:00"), ("13:00", "13:30"), ("14:30", "15:00")],
        "Wednesday": []
    },
    "Joyce": {
        "Monday":   [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "12:30"),
                     ("13:00", "15:00"), ("15:30", "17:00")],
        "Tuesday":  [("09:00", "17:00")],
        "Wednesday":[("09:00", "09:30"), ("10:00", "11:00"), ("12:30", "15:30"), ("16:00", "16:30")]
    }
}

# Convert schedule to minutes
schedule_min: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    person: {
        day: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for day, intervals in days_map.items()
    } for person, days_map in schedule.items()
}

# Find earliest feasible slot honoring constraints
def find_meeting() -> Tuple[str, int, int]:
    for day in days:
        # Free intervals per participant
        free_lists = []
        for person in schedule_min:
            busy = schedule_min[person].get(day, [])
            free = complement_within(work_hours, busy)
            free_lists.append(free)

        # Intersect all participants' free times
        common = free_lists[0]
        for fl in free_lists[1:]:
            common = intersect_intervals(common, fl)
            if not common:
                break

        # Apply preference: Joyce would rather not meet on Monday before 12:00
        if day == "Monday":
            noon = to_minutes("12:00")
            common = clip_intervals(common, (noon, work_hours[1]))

        # Pick the earliest block that fits duration
        for s, e in common:
            if e - s >= duration:
                return day, s, s + duration
    raise ValueError("No feasible meeting time found.")

if __name__ == "__main__":
    day, start, end = find_meeting()
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")