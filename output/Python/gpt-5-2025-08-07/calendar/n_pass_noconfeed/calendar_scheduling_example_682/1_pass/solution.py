from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_intervals(allowed: List[Tuple[int, int]], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Subtract busy intervals from allowed intervals to get free intervals
    free: List[Tuple[int, int]] = []
    busy_sorted = sorted(busy)
    for a_start, a_end in allowed:
        cur = a_start
        for b_start, b_end in busy_sorted:
            if b_end <= cur:
                continue
            if b_start >= a_end:
                break
            if b_start > cur:
                free.append((cur, min(b_start, a_end)))
            cur = max(cur, b_end)
        if cur < a_end:
            free.append((cur, a_end))
    return [(s, e) for s, e in free if s < e]

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res: List[Tuple[int, int]] = []
    a_sorted = sorted(a)
    b_sorted = sorted(b)
    while i < len(a_sorted) and j < len(b_sorted):
        s = max(a_sorted[i][0], b_sorted[j][0])
        e = min(a_sorted[i][1], b_sorted[j][1])
        if s < e:
            res.append((s, e))
        if a_sorted[i][1] < b_sorted[j][1]:
            i += 1
        else:
            j += 1
    return res

def trim_to_duration(slots: List[Tuple[int, int]], duration: int) -> List[Tuple[int, int]]:
    # For each slot, keep it as-is; we will pick an exact start later
    return [(s, e) for s, e in slots if e - s >= duration]

def find_earliest_slot(slots: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    # Return earliest (start, start+duration) that fits
    for s, e in sorted(slots):
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No slot fits the duration")

def main():
    duration_minutes = 30
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    work_window = [(work_start, work_end)]
    days = ["Monday", "Tuesday"]

    # Busy schedules
    busy: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
        "Amanda": {
            "Monday": [(to_minutes("09:00"), to_minutes("10:30")),
                       (to_minutes("11:00"), to_minutes("11:30")),
                       (to_minutes("12:30"), to_minutes("13:00")),
                       (to_minutes("13:30"), to_minutes("14:00")),
                       (to_minutes("14:30"), to_minutes("15:00"))],
            "Tuesday": [(to_minutes("09:00"), to_minutes("09:30")),
                        (to_minutes("10:00"), to_minutes("10:30")),
                        (to_minutes("11:30"), to_minutes("12:00")),
                        (to_minutes("13:30"), to_minutes("14:30")),
                        (to_minutes("15:30"), to_minutes("16:00")),
                        (to_minutes("16:30"), to_minutes("17:00"))],
        },
        "Nathan": {
            "Monday": [(to_minutes("10:00"), to_minutes("10:30")),
                       (to_minutes("11:00"), to_minutes("11:30")),
                       (to_minutes("13:30"), to_minutes("14:30")),
                       (to_minutes("16:00"), to_minutes("16:30"))],
            "Tuesday": [(to_minutes("09:00"), to_minutes("10:30")),
                        (to_minutes("11:00"), to_minutes("13:00")),
                        (to_minutes("13:30"), to_minutes("14:00")),
                        (to_minutes("14:30"), to_minutes("15:30")),
                        (to_minutes("16:00"), to_minutes("16:30"))],
        },
    }

    # Additional constraints as allowed windows per participant per day
    # - Amanda does not want to meet on Tuesday after 11:00
    # - Nathan cannot meet on Monday
    allowed_overrides: Dict[str, Dict[str, List[Tuple[int, int]]]] = {
        "Amanda": {
            "Monday": work_window,
            "Tuesday": [(work_start, to_minutes("11:00"))],  # up to 11:00
        },
        "Nathan": {
            "Monday": [],  # cannot meet Monday
            "Tuesday": work_window,
        },
    }

    for day in days:
        # Compute free intervals per participant under work hours and overrides
        free_all: List[List[Tuple[int, int]]] = []
        for person in ["Amanda", "Nathan"]:
            allowed = allowed_overrides[person].get(day, work_window)
            if not allowed:
                free_all.append([])  # no availability this day
                continue
            # Intersect allowed with work window (safety)
            allowed_effective = intersect_intervals(allowed, work_window)
            # Subtract busy to get free
            busy_today = busy[person].get(day, [])
            free = subtract_intervals(allowed_effective, busy_today)
            free_all.append(free)

        # Intersect all participants' free intervals
        if not free_all or any(len(f) == 0 for f in free_all):
            continue
        common = free_all[0]
        for f in free_all[1:]:
            common = intersect_intervals(common, f)
            if not common:
                break
        if not common:
            continue

        # Find earliest slot of required duration
        feasible = trim_to_duration(common, duration_minutes)
        if not feasible:
            continue
        start, end = find_earliest_slot(feasible, duration_minutes)
        print(day)
        print(f"{to_hhmm(start)}:{to_hhmm(end)}")
        return

    # If here, no slot found (problem statement says a solution exists)
    print("No suitable slot found")

if __name__ == "__main__":
    main()