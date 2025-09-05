def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy, day_start, day_end):
    # busy is a list of tuples (start, end) in minutes, already sorted by start time.
    free = []
    current = day_start
    for start, end in sorted(busy):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_intervals(intervals1, intervals2):
    intersections = []
    for s1, e1 in intervals1:
        for s2, e2 in intervals2:
            start = max(s1, s2)
            end = min(e1, e2)
            if end - start > 0:
                intersections.append((start, end))
    return intersections

# Define working hours: 9:00 to 17:00 (in minutes)
WORK_START = 9 * 60    # 540
WORK_END = 17 * 60     # 1020
MEETING_DURATION = 60  # Meeting duration is 60 minutes

# Participant schedules with meeting times given as (start, end) in HH:MM format.
# Bryan's schedule:
bryan = {
    "Monday": [],
    "Tuesday": [],
    "Wednesday": [],
    "Thursday": [("09:30", "10:00"), ("12:30", "13:00")],
    "Friday": [("10:30", "11:00"), ("14:00", "14:30")]
}

# Nicholas's schedule:
nicholas = {
    "Monday": [("11:30", "12:00"), ("13:00", "15:30")],
    "Tuesday": [("09:00", "09:30"), ("11:00", "13:30"), ("14:00", "16:30")],
    "Wednesday": [("09:00", "09:30"), ("10:00", "11:00"), ("11:30", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
    "Thursday": [("10:30", "11:30"), ("12:00", "12:30"), ("15:00", "15:30"), ("16:30", "17:00")],
    "Friday": [("09:00", "10:30"), ("11:00", "12:00"), ("12:30", "14:30"), ("15:30", "16:00"), ("16:30", "17:00")]
}

def convert_schedule(schedule):
    converted = {}
    for day, meetings in schedule.items():
        # Convert all meeting times to minutes
        converted[day] = [(time_to_minutes(s), time_to_minutes(e)) for s, e in meetings]
    return converted

bryan_schedule = convert_schedule(bryan)
nicholas_schedule = convert_schedule(nicholas)

# Preferences: Bryan would like to avoid Tuesday; Nicholas would rather not meet on Monday or Thursday.
bryan_avoid = {"Tuesday"}
nicholas_avoid = {"Monday", "Thursday"}

# Days to consider (Monday to Friday)
days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]

meeting_found = False
proposed_day = None
proposed_start = None
proposed_end = None

# Try to find a meeting time on a day that does not violate preferences.
for day in days:
    if day in bryan_avoid or day in nicholas_avoid:
        continue

    # Get free intervals for each participant on this day
    bryan_busy = bryan_schedule.get(day, [])
    nicholas_busy = nicholas_schedule.get(day, [])
    bryan_free = get_free_intervals(bryan_busy, WORK_START, WORK_END)
    nicholas_free = get_free_intervals(nicholas_busy, WORK_START, WORK_END)

    # Find common free intervals
    common_free = intersect_intervals(bryan_free, nicholas_free)
    
    # Look for a free interval that can fit a 1-hour meeting.
    for start, end in common_free:
        if end - start >= MEETING_DURATION:
            proposed_day = day
            proposed_start = start
            proposed_end = start + MEETING_DURATION
            meeting_found = True
            break
    if meeting_found:
        break

if meeting_found:
    # Output the meeting time in the format HH:MM:HH:MM and the day of the week.
    print(f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)} {proposed_day}")
else:
    print("No feasible meeting time found.")