# Meeting Scheduler for Amanda and Nathan
# Finds a 30-minute slot within 9:00-17:00 on Monday or Tuesday,
# honoring all given busy times and constraints.

from typing import List, Tuple

Time = Tuple[int, int]  # (start_min, end_min)

def t2m(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def m2t(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def subtract_intervals(base: List[Time], blocks: List[Time]) -> List[Time]:
    # Subtract blocks from base intervals (all half-open [start, end))
    result = []
    for b_start, b_end in sorted(blocks):
        new_base = []
        for a_start, a_end in base:
            if b_end <= a_start or b_start >= a_end:
                new_base.append((a_start, a_end))
            else:
                if a_start < b_start:
                    new_base.append((a_start, max(a_start, b_start)))
                if b_end < a_end:
                    new_base.append((min(a_end, max(b_end, a_start)), a_end))
        base = new_base
    result = base
    return [(s, e) for s, e in result if e > s]

def intersect_lists(a: List[Time], b: List[Time]) -> List[Time]:
    i, j = 0, 0
    res = []
    a = sorted(a)
    b = sorted(b)
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

def clip_to_window(base: List[Time], window: Time) -> List[Time]:
    ws, we = window
    clipped = []
    for s, e in base:
        cs, ce = max(s, ws), min(e, we)
        if cs < ce:
            clipped.append((cs, ce))
    return clipped

# Data
WORK_START, WORK_END = t2m("09:00"), t2m("17:00")
WORK_WINDOW = (WORK_START, WORK_END)
MEETING_MIN = 30

busy = {
    "Amanda": {
        "Monday": [
            (t2m("09:00"), t2m("10:30")),
            (t2m("11:00"), t2m("11:30")),
            (t2m("12:30"), t2m("13:00")),
            (t2m("13:30"), t2m("14:00")),
            (t2m("14:30"), t2m("15:00")),
        ],
        "Tuesday": [
            (t2m("09:00"), t2m("09:30")),
            (t2m("10:00"), t2m("10:30")),
            (t2m("11:30"), t2m("12:00")),
            (t2m("13:30"), t2m("14:30")),
            (t2m("15:30"), t2m("16:00")),
            (t2m("16:30"), t2m("17:00")),
        ],
    },
    "Nathan": {
        "Monday": [
            (t2m("10:00"), t2m("10:30")),
            (t2m("11:00"), t2m("11:30")),
            (t2m("13:30"), t2m("14:30")),
            (t2m("16:00"), t2m("16:30")),
        ],
        "Tuesday": [
            (t2m("09:00"), t2m("10:30")),
            (t2m("11:00"), t2m("13:00")),
            (t2m("13:30"), t2m("14:00")),
            (t2m("14:30"), t2m("15:30")),
            (t2m("16:00"), t2m("16:30")),
        ],
    },
}

# Constraints:
# - Meeting on either Monday or Tuesday
# - Amanda does not want Tuesday after 11:00
# - Nathan cannot meet on Monday
days = ["Tuesday"]  # Monday excluded due to Nathan's constraint

def free_intervals(person: str, day: str) -> List[Time]:
    base = [WORK_WINDOW]
    blocks = busy[person].get(day, [])
    free = subtract_intervals(base, blocks)
    # Apply personal day-specific constraints
    if person == "Amanda" and day == "Tuesday":
        # Only up to 11:00
        free = clip_to_window(free, (WORK_START, t2m("11:00")))
    return free

def find_slot() -> Tuple[str, Time]:
    for day in days:
        # Everyone's free intervals for the day
        amanda_free = free_intervals("Amanda", day)
        nathan_free = free_intervals("Nathan", day)
        common = intersect_lists(amanda_free, nathan_free)
        # Find earliest slot of required duration
        for s, e in common:
            if e - s >= MEETING_MIN:
                return day, (s, s + MEETING_MIN)
    raise ValueError("No suitable slot found.")

if __name__ == "__main__":
    day, (start, end) = find_slot()
    # Output must include both the time range (like {14:30:15:30}) and the day of the week.
    print(day)
    print("{" + f"{m2t(start)}:{m2t(end)}" + "}")