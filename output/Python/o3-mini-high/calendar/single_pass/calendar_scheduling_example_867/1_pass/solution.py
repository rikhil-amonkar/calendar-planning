#!/usr/bin/env python3

def time_to_minutes(t):
    """Convert time string HH:MM to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to time string HH:MM."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_slots, work_start, work_end):
    """Given a list of busy intervals (in minutes) and working hours, return free intervals."""
    free = []
    current = work_start
    for b_start, b_end in sorted(busy_slots):
        if b_start > current:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """Compute the intersection of two lists of intervals."""
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start >= 1:
                intersections.append((start, end))
    return intersections

# Define the schedules for Betty and Scott (times in HH:MM)
schedules = {
    "Betty": {
        "Monday": [("10:00", "10:30"), ("13:30", "14:00"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Tuesday": [("9:00", "9:30"), ("11:30", "12:00"), ("12:30", "13:00"), ("13:30", "14:00"), ("16:30", "17:00")],
        "Wednesday": [("9:30", "10:30"), ("13:00", "13:30"), ("14:00", "14:30")],
        "Thursday": [("9:30", "10:00"), ("11:30", "12:00"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:30", "17:00")]
    },
    "Scott": {
        "Monday": [("9:30", "15:00"), ("15:30", "16:00"), ("16:30", "17:00")],
        "Tuesday": [("9:00", "9:30"), ("10:00", "11:00"), ("11:30", "12:00"), ("12:30", "13:30"), ("14:00", "15:00"), ("16:00", "16:30")],
        "Wednesday": [("9:30", "12:30"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "15:30"), ("16:00", "16:30")],
        "Thursday": [("9:00", "9:30"), ("10:00", "10:30"), ("11:00", "12:00"), ("12:30", "13:00"), ("15:00", "16:00"), ("16:30", "17:00")]
    }
}

# Working hours: 9:00 to 17:00
work_start = time_to_minutes("9:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes

# Additional hard constraints:
# - Betty cannot meet on Monday or Tuesday.
# - On Thursday, Betty cannot meet before 15:00.
# - Scott would prefer to avoid Wednesday.
#
# Therefore, the candidate days (from Monday to Thursday) are:
#   Monday -> disallowed (Betty)
#   Tuesday -> disallowed (Betty)
#   Wednesday -> allowed but Scott wants to avoid it if possible.
#   Thursday -> allowed provided meeting starts at or after 15:00.
#
# We will try Thursday first since it meets both participants' preferences.
candidate_days = ["Thursday", "Wednesday"]

meeting_found = False

for day in candidate_days:
    # Skip day if Betty is not allowed (Monday or Tuesday)
    if day in ["Monday", "Tuesday"]:
        continue

    # Convert busy intervals to minutes for each participant on the given day.
    betty_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedules["Betty"].get(day, [])]
    scott_busy = [(time_to_minutes(start), time_to_minutes(end)) for start, end in schedules["Scott"].get(day, [])]
    
    # Get free intervals during working hours.
    betty_free = get_free_intervals(betty_busy, work_start, work_end)
    scott_free = get_free_intervals(scott_busy, work_start, work_end)
    
    # Apply Betty's additional constraint for Thursday: meeting must start at or after 15:00.
    if day == "Thursday":
        min_allowed = time_to_minutes("15:00")
        adjusted_free = []
        for start, end in betty_free:
            if end <= min_allowed:
                continue
            adjusted_free.append((max(start, min_allowed), end))
        betty_free = adjusted_free

    # Find common free intervals.
    common_free = intersect_intervals(betty_free, scott_free)
    common_free.sort(key=lambda interval: interval[0])
    
    # Look for an interval that can accommodate a 30-minute meeting.
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            meeting_day = day
            meeting_found = True
            break
    if meeting_found:
        break

if meeting_found:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output the day and the time range in the format: Day {HH:MM:HH:MM}
    print(f"{meeting_day} {{{start_str}:{end_str}}}")
else:
    print("No available meeting time found.")