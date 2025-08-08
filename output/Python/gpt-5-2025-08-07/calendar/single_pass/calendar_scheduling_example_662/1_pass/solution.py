from typing import List, Tuple, Dict

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

def subtract_intervals(base: Tuple[int, int], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    # base is [start, end), blocks are merged, within the same base range
    free = []
    cur = base[0]
    for s, e in blocks:
        if e <= cur:
            continue
        if s > cur:
            free.append((cur, s))
        cur = max(cur, e)
        if cur >= base[1]:
            break
    if cur < base[1]:
        free.append((cur, base[1]))
    return free

def intersect_intervals(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    result = []
    while i < len(a) and j < len(b):
        s = max(a[i][0], b[j][0])
        e = min(a[i][1], b[j][1])
        if s < e:
            result.append((s, e))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return result

def find_meeting(
    participants: Dict[str, Dict[str, List[Tuple[str, str]]]],
    days: List[str],
    work_start: str,
    work_end: str,
    duration_min: int
) -> Tuple[str, str, str]:
    ws, we = to_minutes(work_start), to_minutes(work_end)
    for day in days:
        # Build merged busy intervals per participant clipped to work hours
        all_free = []
        for person, schedule in participants.items():
            blocks = [(max(ws, to_minutes(s)), min(we, to_minutes(e))) for s, e in schedule.get(day, [])]
            # Remove invalid or zero-length due to clipping
            blocks = [(s, e) for s, e in blocks if s < e]
            blocks = merge_intervals(blocks)
            free = subtract_intervals((ws, we), blocks)
            all_free.append(free)
        # Intersect all participants' free intervals
        common = all_free[0]
        for free_list in all_free[1:]:
            common = intersect_intervals(common, free_list)
            if not common:
                break
        # Find earliest slot meeting duration
        for s, e in common:
            if e - s >= duration_min:
                start_str = to_hhmm(s)
                end_str = to_hhmm(s + duration_min)
                return day, start_str, end_str
    raise ValueError("No valid meeting time found")

if __name__ == "__main__":
    # Input data
    participants = {
        "Gary": {
            "Monday": [("9:30", "10:00"), ("11:00", "13:00"), ("14:00", "14:30"), ("16:30", "17:00")],
            "Tuesday": [("9:00", "9:30"), ("10:30", "11:00"), ("14:30", "16:00")],
        },
        "David": {
            "Monday": [("9:00", "9:30"), ("10:00", "13:00"), ("14:30", "16:30")],
            "Tuesday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:30"),
                        ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
        },
    }
    days = ["Monday", "Tuesday"]
    work_start = "9:00"
    work_end = "17:00"
    duration_min = 60

    day, start, end = find_meeting(participants, days, work_start, work_end, duration_min)
    print(f"{day} {{{start}:{end}}}")