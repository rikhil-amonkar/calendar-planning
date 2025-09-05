def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def calc_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for start_busy, end_busy in busy:
        if current < start_busy:
            free.append((current, start_busy))
        current = max(current, end_busy)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    common = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find the overlap between the two intervals
        start_common = max(start1, start2)
        end_common = min(end1, end2)
        if start_common < end_common:
            common.append((start_common, end_common))
        # Move to the next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return common

def main():
    meeting_duration = 60  # meeting duration in minutes

    # Define working hours for Monday: 9:00 to 17:00 in minutes from midnight.
    work_start = 9 * 60   # 9:00 -> 540 minutes
    work_end = 17 * 60    # 17:00 -> 1020 minutes
    day_of_week = "Monday"

    # Busy intervals for each participant (in minutes from midnight):
    # Danielle: 9:00-10:00, 10:30-11:00, 14:30-15:00, 15:30-16:00, 16:30-17:00
    danielle_busy = [
        (9 * 60, 10 * 60),
        (10 * 60 + 30, 11 * 60),
        (14 * 60 + 30, 15 * 60),
        (15 * 60 + 30, 16 * 60),
        (16 * 60 + 30, 17 * 60)
    ]

    # Bruce: 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:30-16:00
    bruce_busy = [
        (11 * 60, 11 * 60 + 30),
        (12 * 60 + 30, 13 * 60),
        (14 * 60, 14 * 60 + 30),
        (15 * 60 + 30, 16 * 60)
    ]

    # Eric: 9:00-9:30, 10:00-11:00, 11:30-13:00, 14:30-15:30
    eric_busy = [
        (9 * 60, 9 * 60 + 30),
        (10 * 60, 11 * 60),
        (11 * 60 + 30, 13 * 60),
        (14 * 60 + 30, 15 * 60 + 30)
    ]

    # Calculate free intervals for each participant based on working hours
    danielle_free = calc_free_intervals(danielle_busy, work_start, work_end)
    bruce_free = calc_free_intervals(bruce_busy, work_start, work_end)
    eric_free = calc_free_intervals(eric_busy, work_start, work_end)

    # Compute common free intervals among Danielle and Bruce
    common_free = intersect_intervals(danielle_free, bruce_free)
    # Further intersect with Eric's free intervals to get common slot for all
    common_free = intersect_intervals(common_free, eric_free)

    # Find the first common interval that can accommodate the meeting duration.
    meeting_start = None
    meeting_end = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    if meeting_start is not None:
        start_str = minutes_to_time_str(meeting_start)
        end_str = minutes_to_time_str(meeting_end)
        print(f"{start_str}:{end_str} {day_of_week}")
    else:
        print("No available slot found.")

if __name__ == "__main__":
    main()