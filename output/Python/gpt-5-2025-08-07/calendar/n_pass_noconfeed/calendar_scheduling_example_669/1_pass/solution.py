from typing import List, Tuple

# Helper functions
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

def invert_within_workday(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy = merge_intervals([(max(work_start, s), min(work_end, e)) for s, e in busy if e > work_start and s < work_end])
    free = []
    current = work_start
    for s, e in busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
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

def find_slot(free_intersections: List[Tuple[int, int]], duration: int, prefer_before: int = None) -> Tuple[int, int]:
    # If preference provided, try to find earliest slot starting before that time
    if prefer_before is not None:
        for s, e in free_intersections:
            if e - s >= duration and s < prefer_before:
                return (s, s + duration)
    # Otherwise, pick the earliest available slot
    for s, e in free_intersections:
        if e - s >= duration:
            return (s, s + duration)
    return None

# Problem setup based on the task
work_hours = (to_minutes("09:00"), to_minutes("17:00"))
duration = 30  # minutes

# Participants' busy schedules
busy = {
    "Jean": {
        "Monday": [],
        "Tuesday": [("11:30", "12:00"), ("16:00", "16:30")],
    },
    "Doris": {
        "Monday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:30", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("09:00", "17:00")],
    },
}

# Convert busy times to minutes
busy_minutes = {
    person: {
        day: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for day, intervals in days.items()
    }
    for person, days in busy.items()
}

days_order = ["Monday", "Tuesday"]

# Preference: Doris would rather not meet on Monday after 14:00
preference_monday_before = to_minutes("14:00")

selected_day = None
selected_slot = None

for day in days_order:
    # Compute each participant's free time for the day
    free_by_person = []
    for person in busy_minutes:
        free = invert_within_workday(busy_minutes[person][day], work_hours[0], work_hours[1])
        free_by_person.append(free)
    # Intersect free times across all participants
    common_free = free_by_person[0]
    for others_free in free_by_person[1:]:
        common_free = intersect_intervals(common_free, others_free)

    # Apply preference for Monday
    if day == "Monday":
        slot = find_slot(common_free, duration, prefer_before=preference_monday_before)
        if slot is None:
            slot = find_slot(common_free, duration)
    else:
        slot = find_slot(common_free, duration)

    if slot:
        selected_day = day
        selected_slot = slot
        break

# Output
if selected_day and selected_slot:
    start_str = to_hhmm(selected_slot[0])
    end_str = to_hhmm(selected_slot[1])
    print(f"{{{start_str}:{end_str}}}")
    print(selected_day)
else:
    # Fallback (should not happen given the problem statement guarantees a solution)
    print("{--:--:--:--}")
    print("No suitable day found")