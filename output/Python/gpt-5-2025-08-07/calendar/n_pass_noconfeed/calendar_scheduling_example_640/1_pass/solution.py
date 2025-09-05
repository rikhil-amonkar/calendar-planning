from typing import List, Tuple

def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def normalize_and_merge(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def complement_within(work_start: int, work_end: int, busy: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # Clip busy to work window and merge overlaps
    clipped = []
    for s, e in busy:
        s2, e2 = max(s, work_start), min(e, work_end)
        if s2 < e2:
            clipped.append((s2, e2))
    merged = normalize_and_merge(clipped)

    free = []
    cursor = work_start
    for s, e in merged:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < work_end:
        free.append((cursor, work_end))
    return free

def intersect(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_earliest_slot(schedules, days_order, work_start, work_end, duration_minutes):
    # Pre-parse schedules to minutes
    schedules_minutes = {}
    for person, day_map in schedules.items():
        schedules_minutes[person] = {}
        for day, intervals in day_map.items():
            schedules_minutes[person][day] = [(parse_time(s), parse_time(e)) for s, e in intervals]

    for day in days_order:
        # Compute free intervals per person
        free_lists = []
        for person in schedules_minutes:
            busy = schedules_minutes[person].get(day, [])
            free = complement_within(work_start, work_end, busy)
            free_lists.append(free)

        # Intersect all free lists
        common = free_lists[0]
        for fl in free_lists[1:]:
            common = intersect(common, fl)
            if not common:
                break

        if not common:
            continue

        # Find earliest interval with enough duration
        for s, e in common:
            if e - s >= duration_minutes:
                start_str, end_str = fmt_time(s), fmt_time(s + duration_minutes)
                return day, start_str, end_str

    return None

def main():
    schedules = {
        "Bobby": {
            "Monday": [("14:30", "15:00")],
            "Tuesday": [("9:00", "11:30"), ("12:00", "12:30"), ("13:00", "15:00"), ("15:30", "17:00")],
        },
        "Michael": {
            "Monday": [("9:00", "10:00"), ("10:30", "13:30"), ("14:00", "15:00"), ("15:30", "17:00")],
            "Tuesday": [("9:00", "10:30"), ("11:00", "11:30"), ("12:00", "14:00"), ("15:00", "16:00"), ("16:30", "17:00")],
        },
    }

    work_start = parse_time("9:00")
    work_end = parse_time("17:00")
    duration_minutes = 30
    days_order = ["Monday", "Tuesday"]  # Preference: earliest day then earliest time

    result = find_earliest_slot(schedules, days_order, work_start, work_end, duration_minutes)
    if result:
        day, start_str, end_str = result
        print(f"{{{start_str}:{end_str}}}")
        print(day)
    else:
        # As per problem statement, a solution exists; this is a fallback.
        print("{}")
        print("No available day")

if __name__ == "__main__":
    main()