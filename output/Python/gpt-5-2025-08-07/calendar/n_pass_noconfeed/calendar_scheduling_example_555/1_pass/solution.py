from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
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

def subtract_intervals(base: Tuple[int, int], blocks: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    start, end = base
    free = [(start, end)]
    for b_start, b_end in merge_intervals(blocks):
        new_free = []
        for f_start, f_end in free:
            # No overlap
            if b_end <= f_start or b_start >= f_end:
                new_free.append((f_start, f_end))
            else:
                # Overlap cases split
                if f_start < b_start:
                    new_free.append((f_start, max(f_start, b_start)))
                if b_end < f_end:
                    new_free.append((min(f_end, b_end), f_end))
        free = [(s, e) for s, e in new_free if e > s]
    return free

def intersect_intervals(A: List[Tuple[int, int]], B: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    i = j = 0
    res = []
    A = sorted(A)
    B = sorted(B)
    while i < len(A) and j < len(B):
        s = max(A[i][0], B[j][0])
        e = min(A[i][1], B[j][1])
        if s < e:
            res.append((s, e))
        if A[i][1] < B[j][1]:
            i += 1
        else:
            j += 1
    return res

# Problem data
day = "Monday"
work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
meeting_duration = 30  # minutes

# Evelyn: no meetings; preference: not after 13:00 (meeting must end by 13:00)
evelyn_latest_end = to_minutes("13:00")
evelyn_window = (work_start, min(work_end, evelyn_latest_end))
evelyn_busy = []  # none
evelyn_free = subtract_intervals(evelyn_window, evelyn_busy)

# Randy: busy blocks
randy_busy = [
    (to_minutes("09:00"), to_minutes("10:30")),
    (to_minutes("11:00"), to_minutes("15:30")),
    (to_minutes("16:00"), to_minutes("17:00")),
]
randy_window = (work_start, work_end)
randy_free = subtract_intervals(randy_window, randy_busy)

# Intersect free times
common_free = intersect_intervals(evelyn_free, randy_free)

# Find earliest slot of required duration
proposed_start = proposed_end = None
for s, e in common_free:
    if e - s >= meeting_duration:
        proposed_start = s
        proposed_end = s + meeting_duration
        # Ensure Evelyn's "not after 13:00" (meeting ends by 13:00)
        if proposed_end <= evelyn_latest_end:
            break
        else:
            # Try to shift within [s, e] to end by her latest end
            latest_allowed_start = min(e - meeting_duration, evelyn_latest_end - meeting_duration)
            if latest_allowed_start >= s:
                proposed_start = latest_allowed_start
                proposed_end = proposed_start + meeting_duration
                break
            else:
                proposed_start = proposed_end = None

if proposed_start is None:
    raise ValueError("No feasible time found, but the task guarantees a solution.")

time_range = f"{to_hhmm(proposed_start)}:{to_hhmm(proposed_end)}"
print(day + " " + "{" + time_range + "}")