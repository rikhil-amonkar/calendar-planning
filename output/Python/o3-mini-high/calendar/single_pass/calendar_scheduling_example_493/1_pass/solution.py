def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Sort the busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2):
    i, j = 0, 0
    intersection = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find the overlapping interval
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            intersection.append((start_overlap, end_overlap))
        # Move to the next interval in the list which ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

def main():
    meeting_duration = 30  # duration in minutes
    day = "Monday"
    work_start = 9 * 60   # 09:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes

    # Define busy intervals for each participant (in minutes from midnight)
    schedules = {
        "Tyler": [],
        "Kelly": [],
        "Stephanie": [(11 * 60, 11 * 60 + 30), (14 * 60 + 30, 15 * 60)],
        "Hannah": [],
        "Joe": [(9 * 60, 9 * 60 + 30), (10 * 60, 12 * 60), (12 * 60 + 30, 13 * 60), (14 * 60, 17 * 60)],
        "Diana": [(9 * 60, 10 * 60 + 30), (11 * 60 + 30, 12 * 60), (13 * 60, 14 * 60), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 17 * 60)],
        "Deborah": [(9 * 60, 10 * 60), (10 * 60 + 30, 12 * 60), (12 * 60 + 30, 13 * 60), (13 * 60 + 30, 14 * 60), (14 * 60 + 30, 15 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    }

    # Compute free intervals for every participant within work hours
    free_times = {}
    for person, busy in schedules.items():
        free_times[person] = get_free_intervals(busy, work_start, work_end)

    # Start with one participant's free intervals and intersect with others
    common_free = free_times["Tyler"]
    for person in free_times:
        if person == "Tyler":
            continue
        common_free = intersect_intervals(common_free, free_times[person])

    # Find the earliest available time slot with enough duration
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        meeting_start_str = minutes_to_time(meeting_slot[0])
        meeting_end_str = minutes_to_time(meeting_slot[1])
        # Output in the format HH:MM:HH:MM along with the day of the week
        print(f"{day} {meeting_start_str}:{meeting_end_str}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()