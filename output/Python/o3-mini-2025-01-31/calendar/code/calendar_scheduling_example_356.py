from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes past midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes past midnight to time string 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    """Given a list of busy intervals (tuple of start and end minutes), return free intervals tuple list within work day."""
    free_intervals = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(intervals_list):
    """Intersect a list of free interval lists. Each free interval list is a list of (start, end) tuples.
       Returns a list of intervals that are common to all lists."""
    # Start with intervals that cover the entire day
    common = intervals_list[0]
    for intervals in intervals_list[1:]:
        new_common = []
        for s1, e1 in common:
            for s2, e2 in intervals:
                low = max(s1, s2)
                high = min(e1, e2)
                if low + meeting_duration <= high:
                    new_common.append((low, high))
        common = new_common
        if not common:
            return []
    return common

# Meeting parameters
meeting_duration = 30  # minutes
work_day_start = time_to_minutes("09:00")
work_day_end = time_to_minutes("17:00")
day_of_week = "Monday"

# Busy schedules for each participant (time strings)
schedules = {
    "Katherine": [("12:00", "12:30"), ("13:00", "14:30")],
    "Rebecca":  [], # no meetings
    "Julie": [("09:00", "09:30"), ("10:30", "11:00"), ("13:30", "14:00"), ("15:00", "15:30")],
    "Angela": [("09:00", "10:00"), ("10:30", "11:00"), ("11:30", "14:00"), ("14:30", "15:00"), ("16:30", "17:00")],
    "Nicholas": [("09:30", "11:00"), ("11:30", "13:30"), ("14:00", "16:00"), ("16:30", "17:00")],
    "Carl": [("09:00", "11:00"), ("11:30", "12:30"), ("13:00", "14:30"), ("15:00", "16:00"), ("16:30", "17:00")]
}

# Convert busy times to intervals in minutes
busy_minutes = {}
for person, intervals in schedules.items():
    busy_minutes[person] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

# Convert busy intervals to free intervals for each person
free_intervals = {}

for person, busy in busy_minutes.items():
    free = get_free_intervals(busy, work_day_start, work_day_end)
    # For Angela, she would like to avoid meetings before 15:00 -> adjust her free intervals
    if person == "Angela":
        # Filter/free only after 15:00 (15:00 is 900 minutes)
        new_free = []
        for start, end in free:
            if end <= time_to_minutes("15:00"):
                continue
            new_free.append((max(start, time_to_minutes("15:00")), end))
        free = new_free
    free_intervals[person] = free

# Now, we need to intersect all free intervals
all_free_lists = list(free_intervals.values())
common_free = intersect_intervals(all_free_lists)

# Select the first interval that can accommodate the meeting duration
proposed_meeting = None
for start, end in common_free:
    if end - start >= meeting_duration:
        proposed_meeting = (start, start + meeting_duration)
        break

if proposed_meeting:
    meeting_start, meeting_end = proposed_meeting
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"{meeting_time_str} {day_of_week}")
else:
    print("No meeting time available.")