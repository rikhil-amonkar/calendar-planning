def get_free_intervals(busy, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Working hours: 9:00 to 17:00 (in minutes from midnight)
    WORK_START = 9 * 60      # 540
    WORK_END = 17 * 60       # 1020
    MEETING_DURATION = 30    # minutes
    
    # Pamela's preference: avoid meetings before 16:00 (i.e. before 960 minutes)
    PREFERRED_START = 16 * 60  # 960 minutes

    # Busy schedules (times in minutes from midnight)
    # Monday: Amy is free; Pamela is busy 9:00-10:30 and 11:00-16:30.
    # Tuesday: Amy is free; Pamela is busy 9:00-9:30 and 10:00-17:00.
    # Wednesday:
    #   Amy is busy 11:00-11:30 and 13:30-14:00.
    #   Pamela is busy 9:00-9:30, 10:00-11:00, 11:30-13:30, 14:30-15:00, 16:00-16:30.
    schedules = {
        "Monday": {
            "Amy": [],
            "Pamela": [(9 * 60, 10 * 60 + 30), (11 * 60, 16 * 60 + 30)]
        },
        "Tuesday": {
            "Amy": [],
            "Pamela": [(9 * 60, 9 * 60 + 30), (10 * 60, 17 * 60)]
        },
        "Wednesday": {
            "Amy": [(11 * 60, 11 * 60 + 30), (13 * 60 + 30, 14 * 60)],
            "Pamela": [
                (9 * 60, 9 * 60 + 30),
                (10 * 60, 11 * 60),
                (11 * 60 + 30, 13 * 60 + 30),
                (14 * 60 + 30, 15 * 60),
                (16 * 60, 16 * 60 + 30)
            ]
        }
    }

    # We want to avoid Monday if possible, so we prefer Wednesday first.
    candidate_days = ["Wednesday", "Monday", "Tuesday"]

    meeting_day = None
    meeting_start = None
    meeting_end = None

    for day in candidate_days:
        # Get busy intervals and compute free intervals for both participants
        amy_busy = sorted(schedules[day]["Amy"])
        pam_busy = sorted(schedules[day]["Pamela"])
        amy_free = get_free_intervals(amy_busy, WORK_START, WORK_END)
        pam_free = get_free_intervals(pam_busy, WORK_START, WORK_END)

        # Find common free time between Amy and Pamela
        common_free = intersect_intervals(amy_free, pam_free)

        # Look for a free slot of at least 30 minutes that meets Pamela’s time preference
        for interval in common_free:
            # If the interval starts before 16:00, shift the candidate start time
            candidate_start = max(interval[0], PREFERRED_START)
            if interval[1] - candidate_start >= MEETING_DURATION:
                meeting_day = day
                meeting_start = candidate_start
                meeting_end = candidate_start + MEETING_DURATION
                break
        if meeting_day is not None:
            break

    if meeting_day is not None:
        # Output the meeting time in HH:MM:HH:MM format along with the day.
        print(f"{format_time(meeting_start)}:{format_time(meeting_end)} on {meeting_day}")
    else:
        print("No available meeting slot found.")

if __name__ == "__main__":
    main()