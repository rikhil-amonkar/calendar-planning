def to_minutes(time_str):
    # Converts a HH:MM string into minutes since midnight.
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def to_HHMM(minutes):
    # Converts minutes since midnight into a HH:MM string.
    h = minutes // 60
    m = minutes % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Given busy intervals (as a list of (start, end) in minutes) within work_start and work_end,
    # returns a list of free intervals.
    free = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Computes the intersection of two lists of intervals.
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        a_start, a_end = intervals1[i]
        b_start, b_end = intervals2[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            intersection.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return intersection

def main():
    # Define working hours in minutes (9:00 - 17:00)
    work_start = 9 * 60    # 540 minutes, i.e., 09:00
    work_end = 17 * 60     # 1020 minutes, i.e., 17:00
    meeting_duration = 30  # 30 minutes

    # Define each participant's busy intervals on Monday (in minutes)
    schedules = {
        "Doris": [(9*60, 11*60), (13*60+30, 14*60), (16*60, 16*60+30)],
        "Theresa": [(10*60, 12*60)],
        "Christian": [],  # No meetings; free all day
        "Terry": [(9*60+30, 10*60), (11*60+30, 12*60), (12*60+30, 13*60),
                  (13*60+30, 14*60), (14*60+30, 15*60), (15*60+30, 17*60)],
        "Carolyn": [(9*60, 10*60+30), (11*60, 11*60+30), (12*60, 13*60),
                    (13*60+30, 14*60+30), (15*60, 17*60)],
        "Kyle": [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 13*60),
                 (14*60+30, 17*60)]
    }

    # Compute free intervals for each participant.
    free_times = {}
    for person, busy in schedules.items():
        free_times[person] = get_free_intervals(busy, work_start, work_end)

    # Start with the entire day as free for intersection and narrow down.
    common_free = [(work_start, work_end)]
    for person in schedules:
        common_free = intersect_intervals(common_free, free_times[person])

    # Find the first common free slot that can accommodate the meeting.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    day = "Monday"
    if meeting_slot:
        start_str = to_HHMM(meeting_slot[0])
        end_str = to_HHMM(meeting_slot[1])
        # Output in the format: Day HH:MM:HH:MM
        print(f"{day} {start_str}:{end_str}")
    else:
        print("No available time slot found.")

if __name__ == "__main__":
    main()