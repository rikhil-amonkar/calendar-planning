from typing import List, Tuple

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

def free_from_busy(busy: List[Tuple[int, int]], work_bounds: Tuple[int, int]) -> List[Tuple[int, int]]:
    start, end = work_bounds
    free = []
    current = start
    for b_start, b_end in sorted(busy):
        if b_end <= current:
            continue
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

def intersect_two(a: List[Tuple[int, int]], b: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
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

def find_meeting(common_free: List[Tuple[int, int]], duration: int) -> Tuple[int, int]:
    for s, e in common_free:
        if e - s >= duration:
            return s, s + duration
    raise ValueError("No suitable meeting time found.")

def main():
    day = "Monday"
    work_start, work_end = to_minutes("09:00"), to_minutes("17:00")
    duration = 60  # minutes

    julie_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("11:00"), to_minutes("11:30")),
        (to_minutes("12:00"), to_minutes("12:30")),
        (to_minutes("13:30"), to_minutes("14:00")),
        (to_minutes("16:00"), to_minutes("17:00")),
    ]
    sean_busy = [
        (to_minutes("09:00"), to_minutes("09:30")),
        (to_minutes("13:00"), to_minutes("13:30")),
        (to_minutes("15:00"), to_minutes("15:30")),
        (to_minutes("16:00"), to_minutes("16:30")),
    ]
    lori_busy = [
        (to_minutes("10:00"), to_minutes("10:30")),
        (to_minutes("11:00"), to_minutes("13:00")),
        (to_minutes("15:30"), to_minutes("17:00")),
    ]

    bounds = (work_start, work_end)

    julie_free = free_from_busy(julie_busy, bounds)
    sean_free = free_from_busy(sean_busy, bounds)
    lori_free = free_from_busy(lori_busy, bounds)

    common = intersect_two(julie_free, sean_free)
    common = intersect_two(common, lori_free)

    start, end = find_meeting(common, duration)

    # Output day and time in required format, including braces with HH:MM:HH:MM
    print(day)
    print(f"{{{to_hhmm(start)}:{to_hhmm(end)}}}")

if __name__ == "__main__":
    main()