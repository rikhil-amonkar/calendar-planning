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

def subtract_from_workday(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    # Clip busy intervals to work hours and merge
    clipped = []
    for s, e in busy:
        s = max(s, work_start)
        e = min(e, work_end)
        if s < e:
            clipped.append((s, e))
    merged = merge_intervals(clipped)

    free = []
    current = work_start
    for s, e in merged:
        if current < s:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

# Data setup
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
MEETING_DURATION = 60  # minutes
days = ["Monday", "Tuesday"]

busy_schedules: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
    "Russell": {
        "Monday": [("10:30", "11:00")],
        "Tuesday": [("13:00", "13:30")],
    },
    "Alexander": {
        "Monday": [("09:00", "11:30"), ("12:00", "14:30"), ("15:00", "17:00")],
        "Tuesday": [("09:00", "10:00"), ("13:00", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
    },
}

# Apply constraints/preferences:
# Russell would rather not meet on Tuesday before 13:30 -> treat as unavailable before 13:30 on Tuesday
preference_block = ("09:00", "13:30")
busy_schedules["Russell"]["Tuesday"].append(preference_block)

# Convert busy schedules to minutes
busy_minutes: Dict[str, Dict[str, List[Tuple[int, int]]]] = {}
for person, by_day in busy_schedules.items():
    busy_minutes[person] = {}
    for day in days:
        intervals = by_day.get(day, [])
        busy_minutes[person][day] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def find_meeting() -> Tuple[str, Tuple[int, int]]:
    for day in days:
        # Compute free intervals for each participant
        all_frees: List[List[Tuple[int, int]]] = []
        for person in busy_minutes:
            free = subtract_from_workday(busy_minutes[person][day], WORK_START, WORK_END)
            all_frees.append(free)
        # Intersect all participants' free intervals
        common = all_frees[0]
        for free in all_frees[1:]:
            common = intersect_intervals(common, free)
            if not common:
                break
        # Find earliest slot of required duration
        for s, e in common:
            if e - s >= MEETING_DURATION:
                return day, (s, s + MEETING_DURATION)
    raise ValueError("No suitable meeting time found (unexpected based on problem statement).")

if __name__ == "__main__":
    day, (start, end) = find_meeting()
    print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")