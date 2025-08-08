def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy, window_start, window_end):
    busy_sorted = sorted(busy, key=lambda x: x[0])
    free = []
    current = window_start
    for b in busy_sorted:
        # Only consider the portion of a busy interval that falls within the meeting window.
        if b[1] <= window_start:
            continue
        if b[0] >= window_end:
            break
        b_start = max(b[0], window_start)
        b_end = min(b[1], window_end)
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < window_end:
        free.append((current, window_end))
    return free

def intersect_intervals(list1, list2):
    result = []
    for (s1, e1) in list1:
        for (s2, e2) in list2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end > start:
                result.append((start, end))
    return result

# Meeting settings
meeting_duration = 30  # in minutes
# Due to Harold's constraint, the meeting must end by 13:00.
meeting_window_start = 9 * 60    # 9:00 -> 540 minutes after midnight
meeting_window_end = 13 * 60     # 13:00 -> 780 minutes after midnight

# Busy schedules represented as (start, end) in minutes after midnight.
# Only intervals within the overall workday and meeting window will be considered.
# Jacqueline is busy: 09:00-09:30, 11:00-11:30, 12:30-13:00, (15:30-16:00 omitted)
jacqueline_busy = [
    (9 * 60, 9 * 60 + 30),
    (11 * 60, 11 * 60 + 30),
    (12 * 60 + 30, 13 * 60)
]

# Harold is busy: 10:00-10:30, (13:00-13:30 and 15:00-17:00 omitted because meeting is before 13:00)
harold_busy = [
    (10 * 60, 10 * 60 + 30)
]

# Arthur is busy: 09:00-09:30, 10:00-12:30, (later meetings omitted)
arthur_busy = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 12 * 60 + 30)
]

# Kelly is busy: 09:00-09:30, 10:00-11:00, 11:30-12:30, (later meetings omitted)
kelly_busy = [
    (9 * 60, 9 * 60 + 30),
    (10 * 60, 11 * 60),
    (11 * 60 + 30, 12 * 60 + 30)
]

# Calculate free intervals within the meeting window for each participant.
jacqueline_free = get_free_intervals(jacqueline_busy, meeting_window_start, meeting_window_end)
harold_free = get_free_intervals(harold_busy, meeting_window_start, meeting_window_end)
arthur_free = get_free_intervals(arthur_busy, meeting_window_start, meeting_window_end)
kelly_free = get_free_intervals(kelly_busy, meeting_window_start, meeting_window_end)

# Compute the common free intervals across all participants.
common_free = jacqueline_free
for free in [harold_free, arthur_free, kelly_free]:
    common_free = intersect_intervals(common_free, free)

# Look for the earliest interval that is at least 30 minutes long.
meeting_slot = None
for (start, end) in sorted(common_free):
    if end - start >= meeting_duration:
        meeting_slot = (start, start + meeting_duration)
        break

if meeting_slot:
    start_str = minutes_to_time(meeting_slot[0])
    end_str = minutes_to_time(meeting_slot[1])
    day = "Monday"
    # Output format: HH:MM:HH:MM with the day of the week.
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available meeting slot found.")