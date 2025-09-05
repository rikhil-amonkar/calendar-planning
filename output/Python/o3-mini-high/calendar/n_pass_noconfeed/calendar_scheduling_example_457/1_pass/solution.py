def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_free_intervals(busy, work_start, work_end):
    # Assumes busy intervals are sorted by start time.
    free = []
    current = work_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        # Move current to the later of its current value or the end of the busy interval.
        if end > current:
            current = end
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersection = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Advance the pointer that ends earlier.
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def find_common_slot(participants_busy, work_start, work_end, duration):
    # Compute free intervals for each participant.
    free_intervals = []
    for person, busy in participants_busy.items():
        free = compute_free_intervals(busy, work_start, work_end)
        free_intervals.append(free)
    
    # Compute intersection of everyone's free intervals.
    common = free_intervals[0]
    for other in free_intervals[1:]:
        common = intersect_intervals(common, other)
    
    # Look for the first common interval with at least the required duration.
    for start, end in common:
        if (end - start) >= duration:
            return start, start + duration
    return None

def main():
    # Define work day boundaries (in minutes since midnight).
    work_start = 9 * 60   # 09:00 → 540
    work_end = 17 * 60    # 17:00 → 1020
    meeting_duration = 30 # minutes

    # Busy schedules for participants (times in minutes since midnight).
    participants_busy = {
        "Andrea": [(9 * 60 + 30, 10 * 60 + 30), (13 * 60 + 30, 14 * 60 + 30)],
        "Ruth":   [(12 * 60 + 30, 13 * 60), (15 * 60, 15 * 60 + 30)],
        "Steven": [(10 * 60, 10 * 60 + 30), (11 * 60, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
                   (13 * 60 + 30, 14 * 60), (15 * 60, 16 * 60)],
        "Grace":  [],  # No busy intervals.
        "Kyle":   [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60),
                   (13 * 60 + 30, 15 * 60), (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Elijah": [(9 * 60, 11 * 60), (11 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60),
                   (15 * 60 + 30, 16 * 60), (16 * 60 + 30, 17 * 60)],
        "Lori":   [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30), (12 * 60, 13 * 60 + 30),
                   (14 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)]
    }

    # Find a common free slot.
    slot = find_common_slot(participants_busy, work_start, work_end, meeting_duration)
    if slot:
        start, end = slot
        # Convert back to HH:MM format.
        start_str = minutes_to_str(start)
        end_str = minutes_to_str(end)
        day_of_week = "Monday"
        print(f"{start_str}:{end_str} {day_of_week}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()