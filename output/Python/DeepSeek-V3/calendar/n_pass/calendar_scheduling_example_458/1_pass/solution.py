from typing import List, Dict, Tuple
from collections import defaultdict

def find_meeting_time(
    participants: List[str],
    schedules: Dict[str, List[Tuple[str, str]]],
    preferences: Dict[str, List[Tuple[str, str]]],
    duration_minutes: int,
    work_hours: Tuple[str, str],
    day: str
) -> Tuple[str, str]:
    # Convert all time slots to minutes since midnight for easier comparison
    def time_to_minutes(time_str: str) -> int:
        hh, mm = map(int, time_str.split(':'))
        return hh * 60 + mm

    def minutes_to_time(minutes: int) -> str:
        hh = minutes // 60
        mm = minutes % 60
        return f"{hh:02d}:{mm:02d}"

    work_start, work_end = work_hours
    work_start_min = time_to_minutes(work_start)
    work_end_min = time_to_minutes(work_end)
    duration = duration_minutes

    # Collect all busy intervals for each participant
    busy_intervals = defaultdict(list)
    for participant, intervals in schedules.items():
        for start, end in intervals:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals[participant].append((start_min, end_min))

    # Add preference constraints as busy intervals
    for participant, intervals in preferences.items():
        for start, end in intervals:
            start_min = time_to_minutes(start)
            end_min = time_to_minutes(end)
            busy_intervals[participant].append((start_min, end_min))

    # Merge overlapping or adjacent intervals for each participant
    for participant in busy_intervals:
        intervals = sorted(busy_intervals[participant])
        merged = []
        for interval in intervals:
            if not merged:
                merged.append(interval)
            else:
                last_start, last_end = merged[-1]
                current_start, current_end = interval
                if current_start <= last_end:
                    merged[-1] = (last_start, max(last_end, current_end))
                else:
                    merged.append(interval)
        busy_intervals[participant] = merged

    # Find all possible free intervals for each participant
    free_intervals = defaultdict(list)
    for participant in participants:
        intervals = busy_intervals.get(participant, [])
        free = []
        prev_end = work_start_min
        for start, end in intervals:
            if start > prev_end:
                free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end_min:
            free.append((prev_end, work_end_min))
        free_intervals[participant] = free

    # Find overlapping free intervals across all participants
    common_free = free_intervals[participants[0]]
    for participant in participants[1:]:
        participant_free = free_intervals[participant]
        new_common_free = []
        i = j = 0
        while i < len(common_free) and j < len(participant_free):
            start1, end1 = common_free[i]
            start2, end2 = participant_free[j]
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            if overlap_start < overlap_end:
                new_common_free.append((overlap_start, overlap_end))
            if end1 < end2:
                i += 1
            else:
                j += 1
        common_free = new_common_free

    # Find the first suitable interval
    for start, end in common_free:
        if end - start >= duration:
            meeting_start = start
            meeting_end = meeting_start + duration
            return (
                minutes_to_time(meeting_start),
                minutes_to_time(meeting_end)
            )

    return None, None

if __name__ == "__main__":
    participants = [
        "Wayne", "Melissa", "Catherine", "Gregory", 
        "Victoria", "Thomas", "Jennifer"
    ]
    schedules = {
        "Melissa": [("10:00", "11:00"), ("12:30", "14:00"), ("15:00", "15:30")],
        "Gregory": [("12:30", "13:00"), ("15:30", "16:00")],
        "Victoria": [
            ("9:00", "9:30"), ("10:30", "11:30"), ("13:00", "14:00"),
            ("14:30", "15:00"), ("15:30", "16:30")
        ],
        "Thomas": [("10:00", "12:00"), ("12:30", "13:00"), ("14:30", "16:00")],
        "Jennifer": [
            ("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "13:00"),
            ("13:30", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")
        ]
    }
    preferences = {
        "Wayne": [("9:00", "14:00")]  # Wayne prefers no meetings before 14:00
    }
    duration = 30
    work_hours = ("9:00", "17:00")
    day = "Monday"

    start_time, end_time = find_meeting_time(
        participants, schedules, preferences, duration, work_hours, day
    )

    if start_time and end_time:
        print(f"{day}:{start_time}:{end_time}")
    else:
        print("No suitable time found.")