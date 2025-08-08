from typing import List, Tuple

# Helper function: convert minutes to HH:MM string format
def format_time(minutes: int) -> str:
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Given working hours in minutes (9 AM to 5 PM)
WORK_START = 9 * 60   # 540
WORK_END   = 17 * 60  # 1020
MEETING_DURATION = 60  # in minutes

# Busy intervals for each participant (times in minutes from midnight)
# Format: (start, end)
julie_busy = [(9 * 60, 9 * 60 + 30),      # 9:00 - 9:30
              (11 * 60, 11 * 60 + 30),    # 11:00 - 11:30
              (12 * 60, 12 * 60 + 30),    # 12:00 - 12:30
              (13 * 60 + 30, 14 * 60),    # 13:30 - 14:00
              (16 * 60, 17 * 60)]         # 16:00 - 17:00

sean_busy = [(9 * 60, 9 * 60 + 30),       # 9:00 - 9:30
             (13 * 60, 13 * 60 + 30),     # 13:00 - 13:30
             (15 * 60, 15 * 60 + 30),     # 15:00 - 15:30
             (16 * 60, 16 * 60 + 30)]     # 16:00 - 16:30

lori_busy = [(10 * 60, 10 * 60 + 30),      # 10:00 - 10:30
             (11 * 60, 13 * 60),         # 11:00 - 13:00
             (15 * 60 + 30, 17 * 60)]     # 15:30 - 17:00

# Function to compute free intervals for a participant given their busy slots
def get_free_intervals(busy: List[Tuple[int, int]], work_start: int, work_end: int) -> List[Tuple[int, int]]:
    free = []
    current = work_start
    # Ensure busy intervals are sorted
    for (start, end) in sorted(busy):
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Function to compute the intersection of two lists of intervals
def intersect_intervals(intervals1: List[Tuple[int, int]], intervals2: List[Tuple[int, int]]) -> List[Tuple[int, int]]:
    intersection = []
    for (start1, end1) in intervals1:
        for (start2, end2) in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if start < end:
                intersection.append((start, end))
    return intersection

def main():
    # Compute free intervals for each participant
    julie_free = get_free_intervals(julie_busy, WORK_START, WORK_END)
    sean_free = get_free_intervals(sean_busy, WORK_START, WORK_END)
    lori_free = get_free_intervals(lori_busy, WORK_START, WORK_END)

    # Compute common free intervals among Julie and Sean
    common_free = intersect_intervals(julie_free, sean_free)
    # Now intersect with Lori's free intervals
    common_free = intersect_intervals(common_free, lori_free)
    
    # Find the earliest common interval that can hold the meeting duration
    meeting_slot = None
    for (start, end) in sorted(common_free):
        if end - start >= MEETING_DURATION:
            meeting_slot = (start, start + MEETING_DURATION)
            break

    if meeting_slot:
        start_time, end_time = meeting_slot
        # Meeting is scheduled for Monday based on the constraints
        print(f"Monday, {format_time(start_time)}:{format_time(end_time)}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()