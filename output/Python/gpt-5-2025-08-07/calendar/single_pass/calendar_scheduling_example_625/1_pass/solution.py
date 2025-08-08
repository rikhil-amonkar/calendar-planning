from typing import List, Tuple, Dict

TimeInterval = Tuple[int, int]  # [start_min, end_min)

def to_minutes(hhmm: str) -> int:
    h, m = map(int, hhmm.split(":"))
    return h * 60 + m

def to_hhmm(minutes: int) -> str:
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def subtract_intervals(base: TimeInterval, blocks: List[TimeInterval]) -> List[TimeInterval]:
    """Return segments of base not covered by any blocks."""
    free = [base]
    for b_start, b_end in sorted(blocks):
        next_free = []
        for f_start, f_end in free:
            # No overlap
            if b_end <= f_start or b_start >= f_end:
                next_free.append((f_start, f_end))
                continue
            # Overlap: split where applicable
            if b_start > f_start:
                next_free.append((f_start, b_start))
            if b_end < f_end:
                next_free.append((b_end, f_end))
        free = next_free
    return free

def intersect_lists(a: List[TimeInterval], b: List[TimeInterval]) -> List[TimeInterval]:
    """Intersect two ordered lists of disjoint intervals."""
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

def generate_slots(avails: List[TimeInterval], duration: int) -> List[TimeInterval]:
    slots = []
    for s, e in avails:
        t = s
        while t + duration <= e:
            slots.append((t, t + duration))
            t += 1  # slide by 1 minute to find earliest feasible slot
    return slots

def preference_score(day: str, start_min: int) -> Tuple[int, int, int]:
    # Lower score is better
    # Preference: Tuesday at/after 14:30 (score 0)
    # Then Tuesday before 14:30 (score 1)
    # Then Monday (score 2)
    fourteen_thirty = to_minutes("14:30")
    if day == "Tuesday" and start_min >= fourteen_thirty:
        return (0, start_min, 0)
    if day == "Tuesday" and start_min < fourteen_thirty:
        return (1, start_min, 0)
    # Monday
    return (2, start_min, 0)

def main():
    # Meeting setup
    duration = 30  # minutes
    days = ["Monday", "Tuesday"]
    work_hours = {
        "Monday": (to_minutes("09:00"), to_minutes("17:00")),
        "Tuesday": (to_minutes("09:00"), to_minutes("17:00")),
    }

    # Participants' busy schedules
    busy: Dict[str, Dict[str, List[TimeInterval]]] = {
        "Jeffrey": {
            "Monday": [],
            "Tuesday": [],
        },
        "Harold": {
            "Monday": [
                (to_minutes("09:00"), to_minutes("10:00")),
                (to_minutes("10:30"), to_minutes("17:00")),
            ],
            "Tuesday": [
                (to_minutes("09:00"), to_minutes("09:30")),
                (to_minutes("10:30"), to_minutes("11:30")),
                (to_minutes("12:30"), to_minutes("13:30")),
                (to_minutes("14:30"), to_minutes("15:30")),
                (to_minutes("16:00"), to_minutes("17:00")),
            ],
        },
    }

    # Compute common availability per day
    candidates = []
    for day in days:
        day_window = work_hours[day]
        # Start with the full work window as availability
        common: List[TimeInterval] = [day_window]
        for person in busy:
            person_free = subtract_intervals(day_window, busy[person][day])
            common = intersect_lists(common, person_free)
            if not common:
                break
        if not common:
            continue

        # Generate all possible 30-min slots within common availability
        slots = generate_slots(common, duration)
        for s, e in slots:
            candidates.append((day, s, e))

    # Rank candidates by preferences, then earliest time
    if not candidates:
        raise SystemExit("No feasible slot found, but problem statement guarantees a solution.")
    candidates.sort(key=lambda x: preference_score(x[0], x[1]))

    best_day, best_start, best_end = candidates[0]
    # Format and output
    time_range = f"{to_hhmm(best_start)}:{to_hhmm(best_end)}"
    print(best_day)
    print(time_range)

if __name__ == "__main__":
    main()