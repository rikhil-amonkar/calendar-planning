from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def from_minutes(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

Interval = Tuple[int, int]

def merge_intervals(intervals: List[Interval]) -> List[Interval]:
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

def subtract_intervals(base: List[Interval], busy: List[Interval]) -> List[Interval]:
    # Assumes base and busy are merged (non-overlapping internally)
    result = []
    for b_s, b_e in busy:
        new_result = []
        for s, e in base:
            if b_e <= s or b_s >= e:
                # no overlap
                new_result.append((s, e))
            else:
                # overlap: keep non-overlapping fragments
                if s < b_s:
                    new_result.append((s, b_s))
                if b_e < e:
                    new_result.append((b_e, e))
        base = new_result
    result = base
    return result

def intersect_two(a: List[Interval], b: List[Interval]) -> List[Interval]:
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

def find_meeting():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    work_block = [(work_start, work_end)]
    meeting_minutes = 30

    schedules = {
        "Emily": [("10:00", "10:30"), ("16:00", "16:30")],
        "Mason": [],
        "Maria": [("10:30", "11:00"), ("14:00", "14:30")],
        "Carl": [("09:30", "10:00"), ("10:30", "12:30"), ("13:30", "14:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "David": [("09:30", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "17:00")],
        "Frank": [("09:30", "10:30"), ("11:00", "11:30"), ("12:30", "13:30"), ("14:30", "17:00")],
    }

    # Prepare each participant's free intervals within working hours
    participants_free: List[List[Interval]] = []
    for person, busy_str in schedules.items():
        busy = [(max(work_start, to_minutes(s)), min(work_end, to_minutes(e))) for s, e in busy_str]
        busy = [(s, e) for s, e in busy if s < e]  # clip to work hours
        busy = merge_intervals(busy)
        free = subtract_intervals(work_block[:], busy)
        free = merge_intervals(free)
        participants_free.append(free)

    # Compute common free intervals
    common_free = [(work_start, work_end)]
    for free in participants_free:
        common_free = intersect_two(common_free, free)
        if not common_free:
            break

    # Find earliest slot with required duration
    for s, e in common_free:
        if e - s >= meeting_minutes:
            start_str = from_minutes(s)
            end_str = from_minutes(s + meeting_minutes)
            print(f"{day} {{{start_str}:{end_str}}}")
            return

    # Fallback (shouldn't happen as per problem statement)
    print(f"{day} {{No Available Slot}}")

if __name__ == "__main__":
    find_meeting()