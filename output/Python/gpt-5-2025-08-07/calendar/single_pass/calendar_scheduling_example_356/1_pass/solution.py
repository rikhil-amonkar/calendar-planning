from typing import List, Tuple, Optional

# Meeting parameters
DAY = "Monday"
WORK_START = "09:00"
WORK_END = "17:00"
MEETING_DURATION_MIN = 30  # minutes

# Participants' schedules (busy intervals) for Monday
schedules_str = {
    "Katherine": [("12:00", "12:30"), ("13:00", "14:30")],
    "Rebecca":   [],
    "Julie":     [("09:00", "09:30"), ("10:30", "11:00"), ("13:30", "14:00"), ("15:00", "15:30")],
    "Angela":    [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "14:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Nicholas":  [("09:30", "11:00"), ("11:30", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
    "Carl":      [("09:00", "11:00"), ("11:30", "12:30"), ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")],
}

# Preference: Angela would like to avoid meetings before 15:00
PREFERRED_START = "15:00"  # earliest preferred start time

def to_minutes(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m: int) -> str:
    return f"{m // 60:02d}:{m % 60:02d}"

def has_conflict(start: int, end: int, busy: List[Tuple[int, int]]) -> bool:
    for s, e in busy:
        if start < e and end > s:
            return True
    return False

def find_meeting_time(
    all_schedules: dict,
    work_start: str,
    work_end: str,
    duration: int,
    preferred_start: Optional[str] = None,
) -> Optional[Tuple[int, int]]:
    ws = to_minutes(work_start)
    we = to_minutes(work_end)
    pref = to_minutes(preferred_start) if preferred_start else ws

    # Convert all schedules to minutes
    schedules_min = {
        person: [(to_minutes(s), to_minutes(e)) for s, e in times]
        for person, times in all_schedules.items()
    }

    # Generate candidate start times in 30-minute increments
    step = 30
    latest_start = we - duration

    # Two-phase search: first honoring preference window, then fallback
    phases = []
    pref_window_start = max(ws, pref)
    if pref_window_start <= latest_start:
        phases.append(range(pref_window_start, latest_start + 1, step))
    # Fallback window (before preference)
    if ws <= latest_start and (not phases or pref_window_start > ws):
        phases.append(range(ws, min(pref_window_start, latest_start + 1), step))

    for phase in phases:
        for start in phase:
            end = start + duration
            if end > we:
                continue
            # Check conflicts for all participants
            if all(not has_conflict(start, end, schedules_min[p]) for p in schedules_min):
                return start, end

    return None

def main():
    result = find_meeting_time(
        schedules_str,
        WORK_START,
        WORK_END,
        MEETING_DURATION_MIN,
        preferred_start=PREFERRED_START,
    )

    if not result:
        raise RuntimeError("No feasible meeting time found, but a solution was expected.")
    start_min, end_min = result
    time_range_str = f"{to_hhmm(start_min)}:{to_hhmm(end_min)}"

    # Output: day of the week and the time range in the requested format
    print(DAY)
    print(f"{{{time_range_str}}}")

if __name__ == "__main__":
    main()