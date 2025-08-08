from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    busy_sorted = sorted(busy)
    free = []
    cur = work_start
    for s, e in busy_sorted:
        if e <= cur:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < work_end:
        free.append((cur, work_end))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def slots_of_duration(intervals: List[Tuple[int, int]], duration: int) -> List[Tuple[int, int]]:
    slots = []
    for s, e in intervals:
        t = s
        while t + duration <= e:
            slots.append((t, t + duration))
            # Since we only need the earliest, but to keep general, step by 1 minute
            t += 1
    return slots

# Work hours and meeting duration
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
DURATION = 60  # minutes

# Existing schedules (busy times)
stephanie_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("09:30"), to_minutes("10:00")),
                  (to_minutes("10:30"), to_minutes("11:00")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("14:00"), to_minutes("14:30"))],
    "Tuesday":   [(to_minutes("12:00"), to_minutes("13:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("10:00")),
                  (to_minutes("13:00"), to_minutes("14:00"))]
}

betty_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday":    [(to_minutes("09:00"), to_minutes("10:00")),
                  (to_minutes("11:00"), to_minutes("11:30")),
                  (to_minutes("14:30"), to_minutes("15:00")),
                  (to_minutes("15:30"), to_minutes("16:00"))],
    "Tuesday":   [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("11:30"), to_minutes("12:00")),
                  (to_minutes("12:30"), to_minutes("14:30")),
                  (to_minutes("15:30"), to_minutes("16:00"))],
    "Wednesday": [(to_minutes("10:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("17:00"))]
}

days = ["Monday", "Tuesday", "Wednesday"]

# Preferences/constraints:
# - Prefer to avoid Monday for Stephanie (so search order: Tuesday, Wednesday, Monday)
# - Betty cannot meet on Tuesday after 12:30 (meeting must end no later than 12:30)
preferred_day_order = ["Tuesday", "Wednesday", "Monday"]
tuesday_latest_end = to_minutes("12:30")

# Compute candidate slots per day
candidates: Dict[str, List[Tuple[int, int]]] = {}
for day in days:
    s_free = invert_busy_to_free(stephanie_busy.get(day, []), WORK_START, WORK_END)
    b_free = invert_busy_to_free(betty_busy.get(day, []), WORK_START, WORK_END)
    both_free = intersect_intervals(s_free, b_free)

    # Apply Tuesday constraint for Betty
    if day == "Tuesday":
        constrained = []
        for s, e in both_free:
            constrained.append((s, min(e, tuesday_latest_end)))
        both_free = [(s, e) for s, e in constrained if e - s >= DURATION]

    # Generate 1-hour slots
    slots = slots_of_duration(both_free, DURATION)
    # Keep earliest-first
    candidates[day] = slots

# Choose the earliest slot based on preferred day order
chosen_day = None
chosen_slot = None
for day in preferred_day_order:
    if candidates.get(day):
        chosen_day = day
        chosen_slot = candidates[day][0]
        break

# Output
if chosen_day and chosen_slot:
    start_str = to_hhmm(chosen_slot[0])
    end_str = to_hhmm(chosen_slot[1])
    print(chosen_day)
    print(f"{{{start_str}:{end_str}}}")
else:
    print("No suitable slot found.")