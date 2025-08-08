def minutes_to_time(mins):
    # Since our timeline starts at 9:00 (i.e., 0 = 9:00), add 9 hours.
    hour = 9 + mins // 60
    minute = mins % 60
    return f"{hour:02d}:{minute:02d}"

def get_free_intervals(busy_intervals, work_start=0, work_end=480):
    # Assume busy_intervals is a list of (start, end) in minutes (relative to 9:00)
    free = []
    current = work_start
    # Sort busy intervals just in case
    for s, e in sorted(busy_intervals):
        if s > current:
            free.append((current, s))
        current = max(current, e)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    # Compute intersection of two lists of intervals.
    intersection = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start > 0:
                intersection.append((start, end))
    return intersection

# Meeting duration (in minutes)
meeting_duration = 60

# Working hours are 9:00 to 17:00 -> we use minutes relative to 9:00: 0 to 480

# Bryan's busy schedule (times expressed in minutes from 9:00)
# Only days with meetings are explicitly included, other days are free.
bryan_busy = {
    "Thursday": [(30, 60), (210, 240)],        # 9:30-10:00 and 12:30-13:00
    "Friday":   [(90, 120), (300, 330)]          # 10:30-11:00 and 14:00-14:30
}

# Nicholas's busy schedule (times expressed in minutes from 9:00)
nicholas_busy = {
    "Monday":    [(150, 180), (240, 390)],        # 11:30-12:00 and 13:00-15:30
    "Tuesday":   [(0, 30), (120, 210), (300, 450)], # 9:00-9:30, 11:00-13:30, 14:00-16:30
    "Wednesday": [(0, 30), (60, 120), (150, 270), (300, 330), (360, 450)],
    "Thursday":  [(90, 150), (180, 210), (360, 390), (450, 480)],
    "Friday":    [(0, 90), (120, 180), (210, 330), (390, 420), (450, 480)]
}

# Preferences:
# Bryan prefers to avoid Tuesday.
# Nicholas would rather not meet on Monday or Thursday.
bryan_allowed = {"Monday", "Wednesday", "Thursday", "Friday"}
nicholas_allowed = {"Tuesday", "Wednesday", "Friday"}

# Common allowed days (in order of the week)
days_order = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
common_days = [day for day in days_order if day in (bryan_allowed & nicholas_allowed)]

meeting_day = None
meeting_start = None
meeting_end = None

for day in common_days:
    # Get free intervals for Bryan (if no busy info, assume fully free)
    bryan_free = get_free_intervals(bryan_busy.get(day, []))
    # Get free intervals for Nicholas
    nicholas_free = get_free_intervals(nicholas_busy.get(day, []))
    
    # Intersection of free intervals for both
    common_free = intersect_intervals(bryan_free, nicholas_free)
    
    # Check if any common free interval is at least meeting_duration minutes long
    for start, end in sorted(common_free):
        if end - start >= meeting_duration:
            meeting_day = day
            meeting_start = start
            meeting_end = start + meeting_duration
            break
    if meeting_day is not None:
        break

if meeting_day is not None:
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)
    # Output the day and the time range in HH:MM:HH:MM format
    print(f"{meeting_day} {start_str}:{end_str}")
else:
    print("No suitable meeting time found.")