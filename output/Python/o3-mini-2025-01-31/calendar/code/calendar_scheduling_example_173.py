from datetime import datetime, timedelta

# Define a helper function to convert time string to minutes since midnight
def time_to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

# Define a helper function to convert minutes since midnight to time string in HH:MM format
def minutes_to_time(m):
    return f"{m//60:02d}:{m%60:02d}"

# Workday start and end (in minutes)
workday_start = time_to_minutes("09:00")
workday_end   = time_to_minutes("17:00")

# Meeting duration in minutes
meeting_duration = 30

# Busy intervals for each participant on Monday as tuples (start, end) in minutes
busy_jacqueline = [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                   (time_to_minutes("11:00"), time_to_minutes("11:30")),
                   (time_to_minutes("12:30"), time_to_minutes("13:00")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00"))]

busy_harold = [(time_to_minutes("10:00"), time_to_minutes("10:30")),
               (time_to_minutes("13:00"), time_to_minutes("13:30")),
               (time_to_minutes("15:00"), time_to_minutes("17:00"))]

busy_arthur = [(time_to_minutes("09:00"), time_to_minutes("09:30")),
               (time_to_minutes("10:00"), time_to_minutes("12:30")),
               (time_to_minutes("14:30"), time_to_minutes("15:00")),
               (time_to_minutes("15:30"), time_to_minutes("17:00"))]

busy_kelly = [(time_to_minutes("09:00"), time_to_minutes("09:30")),
              (time_to_minutes("10:00"), time_to_minutes("11:00")),
              (time_to_minutes("11:30"), time_to_minutes("12:30")),
              (time_to_minutes("14:00"), time_to_minutes("15:00")),
              (time_to_minutes("15:30"), time_to_minutes("16:00"))]

# Harold does not want to meet after 13:00. So override his available workday end further for meeting.
harold_meeting_latest = time_to_minutes("13:00")

# A function to compute free intervals given busy intervals and overall time bounds
def get_free_intervals(busy, start, end):
    busy_sorted = sorted(busy)
    free = []
    current = start
    for b_start, b_end in busy_sorted:
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

# Compute free intervals for each participant within Monday work hours
jacqueline_free = get_free_intervals(busy_jacqueline, workday_start, workday_end)
harold_free     = get_free_intervals(busy_harold, workday_start, min(workday_end, harold_meeting_latest))
arthur_free     = get_free_intervals(busy_arthur, workday_start, workday_end)
kelly_free      = get_free_intervals(busy_kelly, workday_start, workday_end)

# For debugging purpose, you could print each free interval if needed:
# print("Jacqueline free:", [(minutes_to_time(s), minutes_to_time(e)) for s,e in jacqueline_free])
# print("Harold free:", [(minutes_to_time(s), minutes_to_time(e)) for s,e in harold_free])
# print("Arthur free:", [(minutes_to_time(s), minutes_to_time(e)) for s,e in arthur_free])
# print("Kelly free:", [(minutes_to_time(s), minutes_to_time(e)) for s,e in kelly_free])

# Function to find the intersection of two lists of intervals
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersections = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        inter_start = max(start1, start2)
        inter_end = min(end1, end2)
        if inter_start + meeting_duration <= inter_end:
            intersections.append((inter_start, inter_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Intersect free intervals step by step for all participants.
common_free = intersect_intervals(jacqueline_free, harold_free)
common_free = intersect_intervals(common_free, arthur_free)
common_free = intersect_intervals(common_free, kelly_free)

# Now select the first interval that can accommodate the meeting duration
proposed_time = None
for start, end in common_free:
    if start + meeting_duration <= end:
        proposed_time = (start, start + meeting_duration)
        break

if proposed_time:
    start_time, end_time = proposed_time
    # Meeting is scheduled on Monday
    day_of_week = "Monday"
    # Output in the specified format: HH:MM:HH:MM and day of week.
    print(f"{day_of_week} {minutes_to_time(start_time)}:{minutes_to_time(end_time)}")
else:
    print("No available meeting time found.")