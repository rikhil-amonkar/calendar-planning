from typing import List, Tuple, Dict

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_busy(available: List[Tuple[int, int]], busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    busy = sorted(busy)
    result = available[:]
    for bs, be in busy:
        new_result = []
        for as_, ae in result:
            if be <= as_ or bs >= ae:
                # no overlap
                new_result.append((as_, ae))
            else:
                # overlap: possibly split
                if bs > as_:
                    new_result.append((as_, bs))
                if be < ae:
                    new_result.append((be, ae))
        result = new_result
    return result

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

# Configuration
DAYS = ["Monday", "Tuesday", "Wednesday"]
WORK_START = to_minutes("09:00")
WORK_END = to_minutes("17:00")
MEETING_DURATION = 30  # minutes

# Participants' constraints
# Busy times per day
cheryl_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("09:00"), to_minutes("09:30")),
               (to_minutes("11:30"), to_minutes("13:00")),
               (to_minutes("15:30"), to_minutes("16:00"))],
    "Tuesday": [(to_minutes("15:00"), to_minutes("15:30"))],
    "Wednesday": []  # She cannot meet on Wednesday; handled below
}

kyle_busy: Dict[str, List[Tuple[int, int]]] = {
    "Monday": [(to_minutes("09:00"), to_minutes("17:00"))],
    "Tuesday": [(to_minutes("09:30"), to_minutes("17:00"))],
    "Wednesday": [(to_minutes("09:00"), to_minutes("09:30")),
                  (to_minutes("10:00"), to_minutes("13:00")),
                  (to_minutes("13:30"), to_minutes("14:00")),
                  (to_minutes("14:30"), to_minutes("17:00"))]
}

# Additional constraints: Cheryl cannot meet on Wednesday
cheryl_unavailable_days = {"Wednesday"}

def day_available_intervals(busy_map: Dict[str, List[Tuple[int, int]]], day: str) -> List[Tuple[int, int]]:
    base = [(WORK_START, WORK_END)]
    busy = busy_map.get(day, [])
    return subtract_busy(base, busy)

def find_meeting() -> Tuple[str, Tuple[int, int]]:
    for day in DAYS:
        if day in cheryl_unavailable_days:
            continue
        cheryl_avail = day_available_intervals(cheryl_busy, day)
        kyle_avail = day_available_intervals(kyle_busy, day)

        common = intersect_intervals(cheryl_avail, kyle_avail)
        for s, e in common:
            if e - s >= MEETING_DURATION:
                start = s
                end = s + MEETING_DURATION
                return day, (start, end)
    raise ValueError("No meeting time found")

if __name__ == "__main__":
    day, (start, end) = find_meeting()
    time_range = f"{to_hhmm(start)}:{to_hhmm(end)}"
    print(f"{day} {{{time_range}}}")