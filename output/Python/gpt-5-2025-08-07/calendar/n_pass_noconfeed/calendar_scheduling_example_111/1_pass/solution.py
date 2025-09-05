from typing import List, Tuple

# Helper functions
def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_time_str(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def merge_intervals(intervals: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def complement_intervals(blocks: List[Tuple[int, int]], window: Tuple[int, int]) -> List[Tuple[int, int]]:
    ws, we = window
    # Clamp blocks to window and merge
    clamped = []
    for s, e in blocks:
        if e <= ws or s >= we:
            continue
        clamped.append((max(s, ws), min(e, we)))
    clamped = merge_intervals(clamped)

    # Build free intervals
    free = []
    cursor = ws
    for s, e in clamped:
        if cursor < s:
            free.append((cursor, s))
        cursor = max(cursor, e)
    if cursor < we:
        free.append((cursor, we))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_earliest_slot(free_sets: List[List[Tuple[int, int]]], duration: int) -> Tuple[int, int]:
    # Intersect all free intervals
    common = free_sets[0]
    for fs in free_sets[1:]:
        common = intersect_two(common, fs)
        if not common:
            break
    # Find earliest interval with enough duration
    for s, e in common:
        if e - s >= duration:
            return s, s + duration
    return None

def main():
    day = "Monday"
    work_window = (to_minutes("09:00"), to_minutes("17:00"))
    duration = 30  # minutes

    # Blocked schedules (inclusive of start, exclusive of end)
    schedules = {
        "Gregory": [("09:00", "10:00"), ("10:30", "11:30"), ("12:30", "13:00"), ("13:30", "14:00")],
        "Natalie": [],  # wide open
        "Christine": [("09:00", "11:30"), ("13:30", "17:00")],
        "Vincent": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "14:00"), ("14:30", "17:00")],
    }

    # Convert to minutes and compute free intervals
    free_sets = []
    for person, blocks in schedules.items():
        blocks_mins = [(to_minutes(s), to_minutes(e)) for s, e in blocks]
        free = complement_intervals(blocks_mins, work_window)
        free_sets.append(free)

    slot = find_earliest_slot(free_sets, duration)
    if not slot:
        print(day)
        print("No available slot")
        return

    start, end = slot
    time_range = f"{to_time_str(start)}:{to_time_str(end)}"
    print(day)
    print(time_range)

if __name__ == "__main__":
    main()