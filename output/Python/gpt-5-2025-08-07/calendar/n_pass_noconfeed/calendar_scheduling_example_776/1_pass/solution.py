from typing import List, Tuple, Dict

# Utility functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy(busy: List[Tuple[int, int]], day_start: int, day_end: int) -> List[Tuple[int, int]]:
    if not busy:
        return [(day_start, day_end)]
    busy = sorted(busy)
    free = []
    cur = day_start
    for s, e in busy:
        if cur < s:
            free.append((cur, s))
        cur = max(cur, e)
    if cur < day_end:
        free.append((cur, day_end))
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

def generate_slots(free: List[Tuple[int, int]], duration: int, step: int = 30) -> List[Tuple[int, int]]:
    slots = []
    for s, e in free:
        start = s + ((-s) % step)  # align to step
        while start + duration <= e:
            slots.append((start, start + duration))
            start += step
    return sorted(slots)

# Schedules (busy times) per participant
# Days considered: Monday, Tuesday, Wednesday
days = ["Monday", "Tuesday", "Wednesday"]
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
duration = 30  # minutes

john_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
}

jennifer_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("09:00"), to_minutes("11:00")),
               (to_minutes("11:30"), to_minutes("13:00")),
               (to_minutes("13:30"), to_minutes("14:30")),
               (to_minutes("15:00"), to_minutes("17:00"))],
    "Tuesday": [(to_minutes("09:00"), to_minutes("11:30")),
                (to_minutes("12:00"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("11:30")),
                  (to_minutes("12:00"), to_minutes("12:30")),
                  (to_minutes("13:00"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("16:00")),
                  (to_minutes("16:30"), to_minutes("17:00"))],
}

# Compute free intervals for each person
def day_free(person_busy: Dict[str, List[Tuple[int, int]]], day: str) -> List[Tuple[int, int]]:
    return invert_busy(person_busy.get(day, []), work_start, work_end)

# Generate candidate slots for each day (intersection of free times)
day_slots: Dict[str, List[Tuple[int, int]]] = {}
for d in days:
    john_free = day_free(john_busy, d)
    jennifer_free = day_free(jennifer_busy, d)
    common_free = intersect_intervals(john_free, jennifer_free)
    slots = generate_slots(common_free, duration, step=30)
    day_slots[d] = slots

# Preferences:
# - Prefer Monday slots that end by 14:30
# - Then any Monday slot
# - Then Tuesday slots
# - Then Wednesday slots
cutoff = to_minutes("14:30")

def pick_slot(day_slots: Dict[str, List[Tuple[int, int]]]) -> Tuple[str, Tuple[int, int]]:
    # Monday before cutoff
    mons = [s for s in day_slots["Monday"] if s[1] <= cutoff]
    if mons:
        return "Monday", mons[0]
    # Any Monday
    if day_slots["Monday"]:
        return "Monday", day_slots["Monday"][0]
    # Tuesday
    if day_slots["Tuesday"]:
        return "Tuesday", day_slots["Tuesday"][0]
    # Wednesday
    if day_slots["Wednesday"]:
        return "Wednesday", day_slots["Wednesday"][0]
    raise ValueError("No available slot found")

chosen_day, (start, end) = pick_slot(day_slots)
start_str = to_hhmm(start)
end_str = to_hhmm(end)

# Output: include both day and time range in HH:MM:HH:MM format, with braces around the time range
print(f"{chosen_day} {{{start_str}:{end_str}}}")