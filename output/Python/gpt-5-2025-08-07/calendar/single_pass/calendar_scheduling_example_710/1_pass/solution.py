from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def invert_busy_to_free(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    free = []
    current = work_start
    for s, e in sorted(busy):
        if e <= current:
            continue
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

# Constraints
meeting_duration = 30  # minutes
work_start = to_minutes("09:00")
work_end = to_minutes("17:00")

days_order = ["Monday", "Tuesday", "Wednesday"]
# Cheryl cannot meet on Wednesday, so exclude it from consideration
allowed_days = ["Monday", "Tuesday"]

busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
    "Cheryl": {
        "Monday": [(to_minutes("09:00"), to_minutes("09:30")),
                   (to_minutes("11:30"), to_minutes("13:00")),
                   (to_minutes("15:30"), to_minutes("16:00"))],
        "Tuesday": [(to_minutes("15:00"), to_minutes("15:30"))],
        # Wednesday excluded by constraint
    },
    "Kyle": {
        "Monday": [(to_minutes("09:00"), to_minutes("17:00"))],
        "Tuesday": [(to_minutes("09:30"), to_minutes("17:00"))],
        "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                      (to_minutes("10:00"), to_minutes("13:00")),
                      (to_minutes("13:30"), to_minutes("14:00")),
                      (to_minutes("14:30"), to_minutes("17:00"))],
    }
}

def find_meeting():
    # Respect original day order but only consider allowed days
    for day in [d for d in days_order if d in allowed_days]:
        # Compute free intervals for each participant on this day
        free_intervals_per_person = []
        for person in busy:
            person_busy = busy[person].get(day, [])
            free = invert_busy_to_free(person_busy, work_start, work_end)
            free_intervals_per_person.append(free)

        # Intersect all participants' free intervals
        common = free_intervals_per_person[0]
        for idx in range(1, len(free_intervals_per_person)):
            common = intersect_intervals(common, free_intervals_per_person[idx])
            if not common:
                break

        # Find earliest slot of required duration
        for s, e in common:
            if e - s >= meeting_duration:
                start = s
                end = s + meeting_duration
                return day, to_time_str(start) + ":" + to_time_str(end)

    return None, None

day, time_range = find_meeting()
if day and time_range:
    # Output must include both the time range (HH:MM:HH:MM) and the day
    print(time_range)
    print(day)
else:
    print("No available slot found.")