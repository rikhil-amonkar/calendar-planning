def time_to_minutes(time_str):
    """Converts a time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Converts minutes since midnight into a time string 'HH:MM'."""
    return f"{m // 60:02d}:{m % 60:02d}"

# Meeting settings
MEETING_DURATION = 30  # in minutes
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
PREFERRED_START = time_to_minutes("16:00")  # Pamela prefers meetings at/after 16:00 on Tue/Wed

# Busy schedules in minutes.
# For each day, we list busy intervals as (start, end) in minutes.
busy = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("10:30")),  # Pamela busy
        (time_to_minutes("11:00"), time_to_minutes("16:30"))   # Pamela busy
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),  # Pamela busy
        (time_to_minutes("10:00"), time_to_minutes("17:00"))   # Pamela busy
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),  # Pamela busy
        (time_to_minutes("10:00"), time_to_minutes("11:00")),  # Pamela busy
        (time_to_minutes("11:00"), time_to_minutes("11:30")),  # Amy busy
        (time_to_minutes("11:30"), time_to_minutes("13:30")),  # Pamela busy
        (time_to_minutes("13:30"), time_to_minutes("14:00")),  # Amy busy
        (time_to_minutes("14:30"), time_to_minutes("15:00")),  # Pamela busy
        (time_to_minutes("16:00"), time_to_minutes("16:30"))   # Pamela busy
    ]
}

def merge_intervals(intervals):
    """Merge overlapping or contiguous intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for current in intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def get_free_intervals(busy_intervals, work_start, work_end):
    """Return a list of free intervals within [work_start, work_end] 
       when given a list of busy intervals."""
    free = []
    merged = merge_intervals(busy_intervals)
    # If work starts before the first busy interval, add that free time.
    if merged:
        if work_start < merged[0][0]:
            free.append((work_start, merged[0][0]))
        for i in range(len(merged) - 1):
            gap_start = merged[i][1]
            gap_end = merged[i+1][0]
            if gap_end - gap_start >= MEETING_DURATION:
                free.append((gap_start, gap_end))
        # After the last busy interval.
        if work_end - merged[-1][1] >= MEETING_DURATION:
            free.append((merged[-1][1], work_end))
    else:
        free.append((work_start, work_end))
    return free

# We will generate candidate meeting slots.
# For each candidate, we store a tuple: (penalty, day, meeting_start, meeting_end)
#
# Pamela’s preferences are:
#   - Avoid Monday completely (high penalty if on Monday).
#   - On Tuesday or Wednesday, avoid meeting times before 16:00 if possible.
# So, on Tue/Wed a candidate that can be scheduled at/after 16:00 gets 0 penalty,
# while a candidate scheduled earlier gets a penalty.
candidates = []

for day in ["Monday", "Tuesday", "Wednesday"]:
    free_intervals = get_free_intervals(busy.get(day, []), WORK_START, WORK_END)
    for free_start, free_end in free_intervals:
        # For Tuesday and Wednesday, if possible, try to schedule the meeting at/after 16:00.
        if day in ("Tuesday", "Wednesday"):
            if free_end >= max(free_start, PREFERRED_START) + MEETING_DURATION:
                candidate_start = max(free_start, PREFERRED_START)
                penalty = 0
            else:
                candidate_start = free_start
                penalty = 50
        elif day == "Monday":
            # Pamela would like to avoid Monday even if the time works.
            if free_end >= max(free_start, PREFERRED_START) + MEETING_DURATION:
                candidate_start = max(free_start, PREFERRED_START)
            else:
                candidate_start = free_start
            penalty = 100
        candidate_end = candidate_start + MEETING_DURATION
        # Ensure the candidate meeting fits in the free block.
        if candidate_end <= free_end:
            candidates.append((penalty, day, candidate_start, candidate_end))

# Choose the candidate with the lowest penalty and, in case of tie, the earliest start time.
if candidates:
    candidates.sort(key=lambda x: (x[0], x[2]))
    best = candidates[0]
    penalty, best_day, best_start, best_end = best
    start_str = minutes_to_time(best_start)
    end_str = minutes_to_time(best_end)
    # Output format: "Day HH:MM:HH:MM"
    print(f"{best_day} {start_str}:{end_str}")
else:
    print("No available meeting time found.")