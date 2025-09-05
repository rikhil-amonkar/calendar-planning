from typing import List, Tuple

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

def get_free_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    # Clamp busy intervals to work hours and merge
    clamped = []
    for s, e in busy:
        if e <= work_start or s >= work_end:
            continue
        clamped.append((max(s, work_start), min(e, work_end)))
    merged_busy = merge_intervals(clamped)
    # Build free intervals from merged busy within work hours
    free = []
    current = work_start
    for s, e in merged_busy:
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def intersect_all(lists: List[List[Tuple[int, int]]]) -> List[Tuple[int, int]]:
    if not lists:
        return []
    result = lists[0]
    for lst in lists[1:]:
        result = intersect_two(result, lst)
        if not result:
            break
    return result

def find_slot(free_intersections: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in free_intersections:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable slot found.")

def main():
    day = "Monday"
    work_start = to_minutes("09:00")
    work_end = to_minutes("17:00")
    duration = 30  # minutes

    schedules = {
        "Shirley": [("10:30", "11:00"), ("12:00", "12:30")],
        "Jacob": [("09:00", "09:30"), ("10:00", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "15:00")],
        "Stephen": [("11:30", "12:00"), ("12:30", "13:00")],
        "Margaret": [("09:00", "09:30"), ("10:30", "12:30"), ("13:00", "13:30"), ("15:00", "15:30"), ("16:30", "17:00")],
        "Mason": [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("16:30", "17:00")],
    }

    # Apply Margaret's constraint: do not want to meet before 14:30 on Monday
    schedules["Margaret"].append(("09:00", "14:30"))

    # Convert to minutes
    busy_minutes = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in intervals]
        for person, intervals in schedules.items()
    }

    # Compute free intervals within work hours for each participant
    free_by_person = [
        get_free_intervals(busy_minutes[person], work_start, work_end)
        for person in ["Shirley", "Jacob", "Stephen", "Margaret", "Mason"]
    ]

    # Find common free intervals
    common_free = intersect_all(free_by_person)

    # Find the earliest slot of the required duration
    start, end = find_slot(common_free, duration)

    start_str = to_hhmm(start)
    end_str = to_hhmm(end)

    # Output day and time range in required format
    print(day)
    print(f"{{{start_str}:{end_str}}}")

if __name__ == "__main__":
    main()