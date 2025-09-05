def time_to_minutes(t):
    """Converts a time string "HH:MM" to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Converts minutes since midnight to a time string "HH:MM"."""
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given a sorted list of busy intervals and the working hours,
    return a list of free intervals within the working hours."""
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
    """Return the intersection of two lists of intervals."""
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            s = max(s1, s2)
            e = min(e1, e2)
            if e - s >= 0:
                intersections.append((s, e))
    return intersections

def filter_intervals(intervals, duration):
    """Filters intervals that are at least 'duration' minutes long."""
    return [(s, e) for s, e in intervals if (e - s) >= duration]

# Meeting parameters
meeting_duration = 30  # minutes
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Busy schedules for Betty and Scott, by day
busy_schedules = {
    'Betty': {
        'Monday': [(time_to_minutes("10:00"), time_to_minutes("10:30")),
                   (time_to_minutes("13:30"), time_to_minutes("14:00")),
                   (time_to_minutes("15:00"), time_to_minutes("15:30")),
                   (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        'Tuesday': [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                    (time_to_minutes("11:30"), time_to_minutes("12:00")),
                    (time_to_minutes("12:30"), time_to_minutes("13:00")),
                    (time_to_minutes("13:30"), time_to_minutes("14:00")),
                    (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        'Wednesday': [(time_to_minutes("09:30"), time_to_minutes("10:30")),
                      (time_to_minutes("13:00"), time_to_minutes("13:30")),
                      (time_to_minutes("14:00"), time_to_minutes("14:30"))],
        'Thursday': [(time_to_minutes("09:30"), time_to_minutes("10:00")),
                     (time_to_minutes("11:30"), time_to_minutes("12:00")),
                     (time_to_minutes("14:00"), time_to_minutes("14:30")),
                     (time_to_minutes("15:00"), time_to_minutes("15:30")),
                     (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    },
    'Scott': {
        'Monday': [(time_to_minutes("09:30"), time_to_minutes("15:00")),
                   (time_to_minutes("15:30"), time_to_minutes("16:00")),
                   (time_to_minutes("16:30"), time_to_minutes("17:00"))],
        'Tuesday': [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                    (time_to_minutes("10:00"), time_to_minutes("11:00")),
                    (time_to_minutes("11:30"), time_to_minutes("12:00")),
                    (time_to_minutes("12:30"), time_to_minutes("13:30")),
                    (time_to_minutes("14:00"), time_to_minutes("15:00")),
                    (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        'Wednesday': [(time_to_minutes("09:30"), time_to_minutes("12:30")),
                      (time_to_minutes("13:00"), time_to_minutes("13:30")),
                      (time_to_minutes("14:00"), time_to_minutes("14:30")),
                      (time_to_minutes("15:00"), time_to_minutes("15:30")),
                      (time_to_minutes("16:00"), time_to_minutes("16:30"))],
        'Thursday': [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                     (time_to_minutes("10:00"), time_to_minutes("10:30")),
                     (time_to_minutes("11:00"), time_to_minutes("12:00")),
                     (time_to_minutes("12:30"), time_to_minutes("13:00")),
                     (time_to_minutes("15:00"), time_to_minutes("16:00")),
                     (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    }
}

# Additional constraints:
#   • Betty cannot meet on Monday and Tuesday.
#   • Betty cannot meet on Thursday before 15:00.
#   • Scott prefers to avoid more meetings on Wednesday.
#
# Thus the only permitted days for Betty are Wednesday and Thursday,
# and Scott's preference nudges us to choose Thursday if available.

# Priority: Try Thursday first, then Wednesday.
candidate_days = ['Thursday', 'Wednesday']

proposed_day = None
proposed_start = None

for day in candidate_days:
    # Skip days not allowed for Betty
    if day in ['Monday', 'Tuesday']:
        continue

    # Get free intervals for both participants within work hours
    betty_busy = busy_schedules['Betty'].get(day, [])
    scott_busy = busy_schedules['Scott'].get(day, [])
    
    betty_free = get_free_intervals(betty_busy, work_start, work_end)
    scott_free = get_free_intervals(scott_busy, work_start, work_end)
    
    # On Thursday, enforce Betty's rule: do not meet before 15:00.
    if day == 'Thursday':
        allowed_start = time_to_minutes("15:00")
        betty_free = [(max(s, allowed_start), e) for s, e in betty_free if e > allowed_start]
    
    # Compute mutual available intervals
    mutual_free = intersect_intervals(betty_free, scott_free)
    mutual_free = filter_intervals(mutual_free, meeting_duration)
    
    if mutual_free:
        mutual_free.sort(key=lambda interval: interval[0])
        proposed_start = mutual_free[0][0]
        proposed_day = day
        break

if proposed_day is not None and proposed_start is not None:
    meeting_start = proposed_start
    meeting_end = meeting_start + meeting_duration
    # Output format: e.g., "Thursday {16:00:16:30}"
    print(f"{proposed_day} {{{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}}}")
else:
    print("No available time slot found.")

if __name__ == "__main__":
    pass