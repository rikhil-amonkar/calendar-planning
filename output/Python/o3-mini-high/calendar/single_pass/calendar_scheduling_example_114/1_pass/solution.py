def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_slots(busy_intervals, work_start, work_end):
    # Returns a list of free time intervals given the busy intervals
    busy_intervals.sort(key=lambda x: x[0])
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Returns the intersection between two lists of intervals
    i, j = 0, 0
    intersected = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersected.append((start, end))
        # Advance the pointer for the interval which ends first
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersected

def main():
    # Define work hours: 9:00 (540 minutes) to 17:00 (1020 minutes)
    work_start = 9 * 60
    work_end = 17 * 60
    meeting_duration = 60  # minutes

    # Busy schedules (times in minutes since midnight)
    # Stephanie is busy from 10:00 to 10:30 and 16:00 to 16:30.
    stephanie_busy = [(10 * 60, 10 * 60 + 30), (16 * 60, 16 * 60 + 30)]
    # Cheryl is busy from 10:00 to 10:30, 11:30 to 12:00, 13:30 to 14:00, 16:30 to 17:00.
    cheryl_busy = [(10 * 60, 10 * 60 + 30),
                   (11 * 60 + 30, 12 * 60),
                   (13 * 60 + 30, 14 * 60),
                   (16 * 60 + 30, 17 * 60)]
    # Bradley is busy from 9:30 to 10:00, 10:30 to 11:30, 13:30 to 14:00, 14:30 to 15:00, and 15:30 to 17:00.
    bradley_busy = [(9 * 60 + 30, 10 * 60),
                    (10 * 60 + 30, 11 * 60 + 30),
                    (13 * 60 + 30, 14 * 60),
                    (14 * 60 + 30, 15 * 60),
                    (15 * 60 + 30, 17 * 60)]
    # Steven is busy from 9:00 to 12:00, 13:00 to 13:30, and 14:30 to 17:00.
    steven_busy = [(9 * 60, 12 * 60),
                   (13 * 60, 13 * 60 + 30),
                   (14 * 60 + 30, 17 * 60)]

    # Calculate free intervals within work hours for each person
    stephanie_free = get_free_slots(stephanie_busy, work_start, work_end)
    cheryl_free = get_free_slots(cheryl_busy, work_start, work_end)
    bradley_free = get_free_slots(bradley_busy, work_start, work_end)
    steven_free = get_free_slots(steven_busy, work_start, work_end)

    # Find the common free intervals among all participants
    common_free = intersect_intervals(stephanie_free, cheryl_free)
    common_free = intersect_intervals(common_free, bradley_free)
    common_free = intersect_intervals(common_free, steven_free)

    # Look for a common free block that can accommodate the meeting duration.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        start_str = minutes_to_time(meeting_slot[0])
        end_str = minutes_to_time(meeting_slot[1])
        # Output the day (Monday) and the meeting time in the format HH:MM:HH:MM.
        print("Monday", f"{start_str}:{end_str}")
    else:
        print("No suitable meeting time found.")

if __name__ == "__main__":
    main()