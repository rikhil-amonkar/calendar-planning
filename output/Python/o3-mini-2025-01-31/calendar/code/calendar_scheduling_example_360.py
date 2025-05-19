def time_to_minutes(t):
    # convert a "HH:MM" string into minutes from midnight
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    # convert minutes from midnight to a "HH:MM" string (zero padded)
    return f"{m//60:02}:{m%60:02}"

def invert_intervals(busy, work_start, work_end):
    # Given a sorted list of busy intervals [(start, end), ...],
    # return the free intervals within [work_start, work_end]
    free = []
    prev_end = work_start
    for start, end in busy:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < work_end:
        free.append((prev_end, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Given two sets of intervals, return their intersection
    intersection = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersection.append((start, end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Work day parameters (in minutes from midnight)
work_day_start = time_to_minutes("09:00")
work_day_end   = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Busy intervals for each participant (each as tuple (start, end) in minutes)
# Times are given in HH:MM format.
participants_busy = {
    "Emily": [(time_to_minutes("10:00"), time_to_minutes("10:30")),
              (time_to_minutes("16:00"), time_to_minutes("16:30"))],
    "Mason": [],  # free all day
    "Maria": [(time_to_minutes("10:30"), time_to_minutes("11:00")),
              (time_to_minutes("14:00"), time_to_minutes("14:30"))],
    "Carl":  [(time_to_minutes("09:30"), time_to_minutes("10:00")),
              (time_to_minutes("10:30"), time_to_minutes("12:30")),
              (time_to_minutes("13:30"), time_to_minutes("14:00")),
              (time_to_minutes("14:30"), time_to_minutes("15:30")),
              (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "David": [(time_to_minutes("09:30"), time_to_minutes("11:00")),
              (time_to_minutes("11:30"), time_to_minutes("12:00")),
              (time_to_minutes("12:30"), time_to_minutes("13:30")),
              (time_to_minutes("14:00"), time_to_minutes("15:00")),
              (time_to_minutes("16:00"), time_to_minutes("17:00"))],
    "Frank": [(time_to_minutes("09:30"), time_to_minutes("10:30")),
              (time_to_minutes("11:00"), time_to_minutes("11:30")),
              (time_to_minutes("12:30"), time_to_minutes("13:30")),
              (time_to_minutes("14:30"), time_to_minutes("17:00"))]
}

# First, compute free intervals for each participant within the work day
participants_free = {}
for person, busy in participants_busy.items():
    # Ensure busy intervals are sorted
    busy_sorted = sorted(busy, key=lambda interval: interval[0])
    free = invert_intervals(busy_sorted, work_day_start, work_day_end)
    participants_free[person] = free

# Now, compute the intersection of free intervals among all participants
common_free = [(work_day_start, work_day_end)]
for free in participants_free.values():
    common_free = intersect_intervals(common_free, free)

# Find a common free interval that is at least meeting_duration minutes long
proposed_meeting = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_meeting = (start, start + meeting_duration)
        break

if proposed_meeting:
    meeting_start = minutes_to_time(proposed_meeting[0])
    meeting_end   = minutes_to_time(proposed_meeting[1])
    day_of_week = "Monday"
    # Output in the requested format: HH:MM:HH:MM and the day of the week
    print(f"{day_of_week} {meeting_start}:{meeting_end}")
else:
    print("No suitable meeting time found.")