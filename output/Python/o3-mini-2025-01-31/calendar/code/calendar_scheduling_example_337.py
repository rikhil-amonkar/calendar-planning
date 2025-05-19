from datetime import datetime, timedelta

# Define working hours for Monday in minutes (9:00 to 17:00)
work_start = 9 * 60    # 9:00 in minutes
work_end = 17 * 60     # 17:00 in minutes

# Meeting duration in minutes (30 minutes)
meeting_duration = 30

# Busy intervals for each participant given in minutes from midnight.
# Each tuple is (start_minute, end_minute)
# Monday: 9:00 = 540, 17:00 = 1020
participants_busy = {
    "John": [(11 * 60 + 30, 12 * 60), (14 * 60, 14 * 60 + 30)],
    "Megan": [(12 * 60, 12 * 60 + 30), (14 * 60, 15 * 60), (15 * 60 + 30, 16 * 60)],
    "Brandon": [],
    "Kimberly": [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (11 * 60, 14 * 60 + 30),
                  (15 * 60, 16 * 60), (16 * 60 + 30, 17 * 60)],
    "Sean": [(10 * 60, 11 * 60), (11 * 60 + 30, 14 * 60), (15 * 60, 15 * 60 + 30)],
    "Lori": [(9 * 60, 9 * 60 + 30), (10 * 60 + 30, 12 * 60), (13 * 60, 14 * 60 + 30),
             (16 * 60, 16 * 60 + 30)]
}

def invert_busy_intervals(busy_intervals, start, end):
    """
    Given a list of busy intervals (start, end) and the overall working time boundaries,
    return a list of free intervals. It is assumed that busy_intervals do not overlap.
    """
    free_intervals = []
    current = start
    for interval in sorted(busy_intervals):
        busy_start, busy_end = interval
        if busy_start > current:
            free_intervals.append((current, busy_start))
        current = max(current, busy_end)
    if current < end:
        free_intervals.append((current, end))
    return free_intervals

# Get free intervals for each participant
participants_free = {}
for person, busy in participants_busy.items():
    # Merge busy intervals with working hours boundary
    free = invert_busy_intervals(busy, work_start, work_end)
    participants_free[person] = free

def intersect_intervals(int1, int2):
    """
    Intersect two lists of intervals.
    Each interval is a tuple (start, end). Return the intersected intervals.
    """
    i, j = 0, 0
    result = []
    while i < len(int1) and j < len(int2):
        start = max(int1[i][0], int2[j][0])
        end = min(int1[i][1], int2[j][1])
        if start < end:
            result.append((start, end))
        # advance the interval which ends earlier
        if int1[i][1] < int2[j][1]:
            i += 1
        else:
            j += 1
    return result

# Compute the overall intersection of free intervals across all participants.
all_free = [(work_start, work_end)]
for free in participants_free.values():
    all_free = intersect_intervals(all_free, free)

# Find a free interval that can fit a meeting of the required duration.
meeting_time = None
for interval in all_free:
    start, end = interval
    if end - start >= meeting_duration:
        meeting_time = (start, start + meeting_duration)
        break

if meeting_time:
    # Convert minutes back to HH:MM format.
    start_minutes, end_minutes = meeting_time
    start_time = f"{start_minutes // 60:02d}:{start_minutes % 60:02d}"
    end_time = f"{end_minutes // 60:02d}:{end_minutes % 60:02d}"
    # For this task, the meeting is on Monday.
    day = "Monday"
    print(f"{day} {start_time}:{end_time}")
else:
    print("No possible meeting time found.")