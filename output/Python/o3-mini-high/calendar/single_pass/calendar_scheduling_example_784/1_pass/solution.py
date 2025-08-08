def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals = sorted(intervals, key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(blocked, work_start, work_end):
    """
    Given a list of blocked intervals and the boundaries of the work day,
    return the free intervals within [work_start, work_end].
    Each interval is represented in minutes.
    """
    merged_blocked = merge_intervals(blocked)
    free = []
    pointer = work_start
    for interval in merged_blocked:
        if pointer < interval[0]:
            free.append((pointer, interval[0]))
        pointer = max(pointer, interval[1])
    if pointer < work_end:
        free.append((pointer, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Intersect two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    """
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersection.append((start, end))
        # Move the pointer that ends earlier.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersection

def minutes_to_str(minutes):
    """Convert minutes since midnight to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Work day boundaries in minutes (9:00 to 17:00)
WORK_START = 9 * 60    # 540
WORK_END = 17 * 60     # 1020
MEETING_DURATION = 60  # minutes

# Define the blocked intervals for each participant (times in minutes)
# Judith's blocked slots:
schedules_judith = {
    "Monday": [(12 * 60, 12 * 60 + 30)],          # 12:00 - 12:30
    "Tuesday": [],                                 # No blocks on Tuesday
    "Wednesday": [(11 * 60 + 30, 12 * 60)]          # 11:30 - 12:00
}

# Timothy's blocked slots:
schedules_timothy = {
    "Monday": [
        (9 * 60 + 30, 10 * 60),                    # 9:30 - 10:00
        (10 * 60 + 30, 11 * 60 + 30),              # 10:30 - 11:30
        (12 * 60 + 30, 14 * 60),                   # 12:30 - 14:00
        (15 * 60 + 30, 17 * 60)                    # 15:30 - 17:00
    ],
    "Tuesday": [
        (9 * 60 + 30, 13 * 60),                    # 9:30 - 13:00
        (13 * 60 + 30, 14 * 60),                   # 13:30 - 14:00
        (14 * 60 + 30, 17 * 60)                    # 14:30 - 17:00
    ],
    "Wednesday": [
        (9 * 60, 9 * 60 + 30),                     # 9:00 - 9:30
        (10 * 60 + 30, 11 * 60),                   # 10:30 - 11:00
        (13 * 60 + 30, 14 * 60 + 30),              # 13:30 - 14:30
        (15 * 60, 15 * 60 + 30),                   # 15:00 - 15:30
        (16 * 60, 16 * 60 + 30)                    # 16:00 - 16:30
    ]
}

# Allowed days and preference order.
# Judith prefers to avoid Monday if possible.
# Also, if the meeting is on Wednesday, it must not start before 12:00.
# We'll try days in the order: Tuesday, Wednesday, then Monday.
days_preference = ["Tuesday", "Wednesday", "Monday"]

def find_meeting_slot():
    for day in days_preference:
        # Get Judith's free intervals for this day.
        blocked_judith = schedules_judith.get(day, [])
        free_judith = get_free_intervals(blocked_judith, WORK_START, WORK_END)

        # Get Timothy's free intervals for this day.
        blocked_timothy = schedules_timothy.get(day, [])
        free_timothy = get_free_intervals(blocked_timothy, WORK_START, WORK_END)

        # Intersection of free intervals for both participants.
        common_free = intersect_intervals(free_judith, free_timothy)

        # Check each common free interval for possibility of a meeting.
        for interval in common_free:
            start, end = interval
            # For Wednesday, adjust to start no earlier than 12:00 (i.e., 720 minutes)
            if day == "Wednesday" and start < 12 * 60:
                start = 12 * 60
            if end - start >= MEETING_DURATION:
                meeting_start = start
                meeting_end = start + MEETING_DURATION
                return day, meeting_start, meeting_end
    return None, None, None  # If no suitable slot is found (should not happen per problem statement)

if __name__ == "__main__":
    day, meeting_start, meeting_end = find_meeting_slot()
    if day is not None:
        # Format the time in HH:MM:HH:MM format followed by the day.
        meeting_time_str = f"{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)}"
        print(f"{meeting_time_str} on {day}")
    else:
        print("No available meeting slot found.")