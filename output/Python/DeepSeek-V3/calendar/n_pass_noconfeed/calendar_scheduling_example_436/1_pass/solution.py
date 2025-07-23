from typing import List, Dict, Tuple
from datetime import time

def find_meeting_time(participants: Dict[str, List[Tuple[time, time]]], duration: int, work_start: time, work_end: time) -> Tuple[str, Tuple[time, time]]:
    # Convert all busy intervals to minutes since start of day
    work_start_min = work_start.hour * 60 + work_start.minute
    work_end_min = work_end.hour * 60 + work_end.minute
    duration_min = duration
    
    # Collect all busy intervals
    busy_intervals = []
    for person, intervals in participants.items():
        for start, end in intervals:
            start_min = start.hour * 60 + start.minute
            end_min = end.hour * 60 + end.minute
            busy_intervals.append((start_min, end_min))
    
    # Sort intervals by start time
    busy_intervals.sort()
    
    # Merge overlapping or adjacent intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:
                new_end = max(last_end, current_end)
                merged[-1] = (last_start, new_end)
            else:
                merged.append(interval)
    
    # Find available slots
    available_slots = []
    prev_end = work_start_min
    for start, end in merged:
        if start > prev_end:
            available_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end_min:
        available_slots.append((prev_end, work_end_min))
    
    # Find the first available slot that can fit the duration
    for slot_start, slot_end in available_slots:
        if slot_end - slot_start >= duration_min:
            meeting_start = slot_start
            meeting_end = meeting_start + duration_min
            # Convert back to time objects
            start_time = time(meeting_start // 60, meeting_start % 60)
            end_time = time(meeting_end // 60, meeting_end % 60)
            return ("Monday", (start_time, end_time))
    
    return ("No available slot found", (None, None))

def main():
    # Define participants and their busy intervals
    participants = {
        "Patrick": [
            (time(13, 30), time(14, 0)),
            (time(14, 30), time(15, 0))
        ],
        "Shirley": [
            (time(9, 0), time(9, 30)),
            (time(11, 0), time(11, 30)),
            (time(12, 0), time(12, 30)),
            (time(14, 30), time(15, 0)),
            (time(16, 0), time(17, 0))
        ],
        "Jeffrey": [
            (time(9, 0), time(9, 30)),
            (time(10, 30), time(11, 0)),
            (time(11, 30), time(12, 0)),
            (time(13, 0), time(13, 30)),
            (time(16, 0), time(17, 0))
        ],
        "Gloria": [
            (time(11, 30), time(12, 0)),
            (time(15, 0), time(15, 30))
        ],
        "Nathan": [
            (time(9, 0), time(9, 30)),
            (time(10, 30), time(12, 0)),
            (time(14, 0), time(17, 0))
        ],
        "Angela": [
            (time(9, 0), time(9, 30)),
            (time(10, 0), time(11, 0)),
            (time(12, 30), time(15, 0)),
            (time(15, 30), time(16, 30))
        ],
        "David": [
            (time(9, 0), time(9, 30)),
            (time(10, 0), time(10, 30)),
            (time(11, 0), time(14, 0)),
            (time(14, 30), time(16, 30))
        ]
    }
    
    # Meeting constraints
    duration = 30  # minutes
    work_start = time(9, 0)
    work_end = time(17, 0)
    
    # Find meeting time
    day, (start_time, end_time) = find_meeting_time(participants, duration, work_start, work_end)
    
    # Output the result
    if start_time and end_time:
        print(f"{day}: {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()