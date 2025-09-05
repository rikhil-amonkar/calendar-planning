from typing import List, Tuple, Dict

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m//60:02d}:{m%60:02d}"

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

def subtract_interval(base: Interval, sub: Interval) -> List[Interval]:
    b_start, b_end = base
    s_start, s_end = sub
    if s_end <= b_start or s_start >= b_end:
        return [base]
    res = []
    if s_start > b_start:
        res.append((b_start, min(s_start, b_end)))
    if s_end < b_end:
        res.append((max(s_end, b_start), b_end))
    return [(s, e) for s, e in res if e > s]

def subtract_intervals(base_list: List[Interval], subs: List[Interval]) -> List[Interval]:
    subs = merge_intervals(subs)
    free = base_list[:]
    for sub in subs:
        new_free = []
        for fr in free:
            new_free.extend(subtract_interval(fr, sub))
        free = new_free
    return free

def intersect_two_lists(a: List[Interval], b: List[Interval]) -> List[Interval]:
    i = j = 0
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

def hhmm_list_to_minutes(intervals: List[Tuple[str, str]]) -> List[Interval]:
    return [(to_minutes(s), to_minutes(e)) for s, e in intervals]

def main():
    meeting_duration = 30  # minutes
    days = ["Monday", "Tuesday"]

    work_hours = {
        "Monday": ("09:00", "17:00"),
        "Tuesday": ("09:00", "17:00"),
    }

    busy_str: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
        "Margaret": {
            "Monday": [("10:30","11:00"), ("11:30","12:00"), ("13:00","13:30"), ("15:00","17:00")],
            "Tuesday": [("12:00","12:30")],
        },
        "Alexis": {
            "Monday": [("09:30","11:30"), ("12:30","13:00"), ("14:00","17:00")],
            "Tuesday": [("09:00","09:30"), ("10:00","10:30"), ("14:00","16:30")],
        },
    }

    # Preferences/constraints:
    # Margaret does not want Monday, and not Tuesday before 14:30
    participant_allowed_str: Dict[str, Dict[str, List[Tuple[str, str]]]] = {
        "Margaret": {
            "Monday": [],                       # disallow Monday
            "Tuesday": [("14:30","17:00")],     # only after 14:30
        },
        "Alexis": {
            "Monday": [("09:00","17:00")],
            "Tuesday": [("09:00","17:00")],
        },
    }

    # Convert to minutes
    work_hours_min = {d: (to_minutes(s), to_minutes(e)) for d, (s, e) in work_hours.items()}
    busy: Dict[str, Dict[str, List[Interval]]] = {
        p: {d: hhmm_list_to_minutes(lst) for d, lst in days_map.items()} for p, days_map in busy_str.items()
    }
    participant_allowed: Dict[str, Dict[str, List[Interval]]] = {
        p: {d: hhmm_list_to_minutes(lst) for d, lst in days_map.items()} for p, days_map in participant_allowed_str.items()
    }

    for day in days:
        # If any participant has no allowed windows for the day, treat as disallowed for them.
        day_work = work_hours_min[day]
        day_work_interval = [day_work]

        participants_common: List[Interval] = None

        for participant in busy:
            # Start with work hours as availability
            free = day_work_interval[:]

            # Subtract busy times
            free = subtract_intervals(free, busy[participant].get(day, []))

            # Apply participant-specific allowed windows
            allowed_windows = participant_allowed.get(participant, {}).get(day, [day_work])
            if not allowed_windows:
                free = []
            else:
                allowed_min = allowed_windows
                # Intersect free with allowed_min
                allowed_intervals = []
                for fr in free:
                    allowed_intervals.extend(intersect_two_lists([fr], allowed_min))
                free = merge_intervals(allowed_intervals)

            # Accumulate intersection across participants
            if participants_common is None:
                participants_common = free
            else:
                participants_common = intersect_two_lists(participants_common, free)

            if not participants_common:
                break

        if not participants_common:
            continue

        # Find earliest slot meeting the duration
        for s, e in participants_common:
            if e - s >= meeting_duration:
                start = s
                end = s + meeting_duration
                print(f"{day} {{{to_hhmm(start)}:{to_hhmm(end)}}}")
                return

    raise RuntimeError("No feasible meeting time found.")

if __name__ == "__main__":
    main()