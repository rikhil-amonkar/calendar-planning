from datetime import timedelta, datetime

# Helper functions to convert times to minutes and back
def time_to_minutes(t_str):
    # t_str in "H:MM" or "HH:MM", assume 24-hour format
    t = datetime.strptime(t_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_time(m):
    hours = m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

# Define working day boundaries in minutes (9:00 to 17:00)
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
MEETING_DURATION = 60  # minutes

# Busy schedules for each participant, keyed by day of week.
# Times are in HH:MM string format.
bryan_busy = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": [("09:30", "10:00"), ("12:30", "13:00")],
    "Friday": [("10:30", "11:00"), ("14:00", "14:30")]
}

nicholas_busy = {
    "Monday": [("11:30", "12:00"), ("13:00", "15:30")],
    "Tuesday": [("09:00", "09:30"), ("11:00", "13:30"), ("14:00", "16:30")],
    "Wednesday": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "13:30"),
                  ("14:00", "14:30"), ("15:00", "16:30")],
    "Thursday": [("10:30", "11:30"), ("12:00", "12:30"), ("15:00", "15:30"), ("16:30", "17:00")],
    "Friday": [("09:00", "10:30"), ("11:00", "12:00"), ("12:30", "14:30"),
               ("15:30", "16:00"), ("16:30", "17:00")]
}

# Preferences: Bryan would like to avoid Tuesday; Nicholas would rather not meet on Monday or Thursday.
avoid_day = {
    "Bryan": {"Tuesday"},
    "Nicholas": {"Monday", "Thursday"}
}

# Function to compute free time intervals given busy periods on a day.
def compute_free_intervals(busy, start=WORK_START, end=WORK_END):
    # Convert busy times to minutes and sort them
    busy_minutes = []
    for period in busy:
        busy_minutes.append((time_to_minutes(period[0]), time_to_minutes(period[1])))
    busy_minutes.sort()

    free = []
    current = start
    for b_start, b_end in busy_minutes:
        if current < b_start:
            free.append((current, b_start))
        current = max(current, b_end)
    if current < end:
        free.append((current, end))
    return free

# Function to compute intersection of two lists of intervals.
def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlap
        overlap_start = max(start1, start2)
        overlap_end = min(end1, end2)
        if overlap_start < overlap_end:
            result.append((overlap_start, overlap_end))
        # Move the pointer which ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Days of week to check in order.
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

# Collect candidate meeting slots per day; store tuples (day, start, end)
candidates = []
for day in days:
    bryan_free = compute_free_intervals(bryan_busy.get(day, []))
    nicholas_free = compute_free_intervals(nicholas_busy.get(day, []))
    common = intersect_intervals(bryan_free, nicholas_free)
    # Check for any common interval that can accommodate MEETING_DURATION minutes.
    for start, end in common:
        if end - start >= MEETING_DURATION:
            candidates.append((day, start, start + MEETING_DURATION))
            break  # We choose the earliest available block on that day

# Now apply preferences:
# We prefer days that are not in the avoid sets.
def preference_score(day):
    score = 0
    if day in avoid_day["Bryan"]:
        score += 1
    if day in avoid_day["Nicholas"]:
        score += 1
    return score

# Among candidates, we select the one with the lowest preference score.
candidates_sorted = sorted(candidates, key=lambda c: (preference_score(c[0]), days.index(c[0])))
if candidates_sorted:
    chosen_day, meeting_start, meeting_end = candidates_sorted[0]
    meeting_time_str = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    print(f"{chosen_day} {meeting_time_str}")
else:
    print("No possible meeting time found.")