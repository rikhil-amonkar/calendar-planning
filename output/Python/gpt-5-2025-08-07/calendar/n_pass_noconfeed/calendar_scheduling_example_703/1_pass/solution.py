from typing import List, Tuple

def time_to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def subtract_interval(free: List[Tuple[int, int]], block: Tuple[int, int]) -> List[Tuple[int, int]]:
    bs, be = block
    result = []
    for fs, fe in free:
        if be <= fs or bs >= fe:
            result.append((fs, fe))
        else:
            if bs > fs:
                result.append((fs, bs))
            if be < fe:
                result.append((be, fe))
    return result

def subtract_intervals(free: List[Tuple[int, int]], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    for block in sorted(blocks):
        free = subtract_interval(free, block)
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    intersections = []
    for s1, e1 in a:
        for s2, e2 in b:
            s, e = max(s1, s2), min(e1, e2)
            if s < e:
                intersections.append((s, e))
    intersections.sort()
    return intersections

def find_meeting_slot(duration: int) -> Tuple[str, str, str]:
    # Work hours
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")
    work_window = [(work_start, work_end)]

    # Existing schedules
    stephanie = {
        "Monday":    [("09:30","10:00"), ("10:30","11:00"), ("11:30","12:00"), ("14:00","14:30")],
        "Tuesday":   [("12:00","13:00")],
        "Wednesday": [("09:00","10:00"), ("13:00","14:00")],
    }

    betty = {
        "Monday":    [("09:00","10:00"), ("11:00","11:30"), ("14:30","15:00"), ("15:30","16:00")],
        "Tuesday":   [("09:00","09:30"), ("11:30","12:00")],
        "Wednesday": [("10:00","11:30"), ("12:00","14:00"), ("14:30","17:00")],
    }

    # Hard constraint: Betty cannot meet on Tuesday after 12:30
    betty["Tuesday"].append(("12:30", "17:00"))

    # Convert schedules to minutes
    def to_minutes(schedule):
        m = {}
        for day, blocks in schedule.items():
            m[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in blocks]
        return m

    steph_m = to_minutes(stephanie)
    betty_m = to_minutes(betty)

    # Preference: avoid Monday if possible
    day_order = ["Tuesday", "Wednesday", "Monday"]

    for day in day_order:
        steph_free = subtract_intervals(work_window[:], steph_m.get(day, []))
        betty_free = subtract_intervals(work_window[:], betty_m.get(day, []))
        common = intersect_intervals(steph_free, betty_free)

        for s, e in common:
            if e - s >= duration:
                start_str = minutes_to_time(s)
                end_str = minutes_to_time(s + duration)
                return day, start_str, end_str

    # Fallback (should not happen given problem guarantees)
    raise RuntimeError("No suitable meeting time found.")

if __name__ == "__main__":
    duration_minutes = 60
    day, start, end = find_meeting_slot(duration_minutes)
    print(f"{day} {{{start}:{end}}}")