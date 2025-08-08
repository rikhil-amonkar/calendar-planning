def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    intersection = []
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        intersect_start = max(start1, start2)
        intersect_end = min(end1, end2)
        if intersect_start < intersect_end:
            intersection.append((intersect_start, intersect_end))
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersection

# Schedules for Megan and Daniel
megan_schedule = {
    "Monday": [("13:00", "13:30"), ("14:00", "15:30")],
    "Tuesday": [("09:00", "09:30"), ("12:00", "12:30"), ("16:00", "17:00")],
    "Wednesday": [("09:30", "10:00"), ("10:30", "11:30"), ("12:30", "14:00"), ("16:00", "16:30")],
    "Thursday": [("13:30", "14:30"), ("15:00", "15:30")]
}

daniel_schedule = {
    "Monday": [("10:00", "11:30"), ("12:30", "15:00")],
    "Tuesday": [("09:00", "10:00"), ("10:30", "17:00")],
    "Wednesday": [("09:00", "10:00"), ("10:30", "11:30"), ("12:00", "17:00")],
    "Thursday": [("09:00", "12:00"), ("12:30", "14:30"), ("15:00", "15:30"), ("16:00", "17:00")]
}

# Convert all busy times to minutes for each day
for day, intervals in megan_schedule.items():
    megan_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

for day, intervals in daniel_schedule.items():
    daniel_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

# Define working hours and meeting duration (in minutes)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 60
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

meeting_day = None
meeting_start = None

for day in days:
    # Get busy intervals and compute free intervals for each participant on a given day
    megan_busy = sorted(megan_schedule.get(day, []))
    daniel_busy = sorted(daniel_schedule.get(day, []))
    
    megan_free = get_free_intervals(megan_busy, work_start, work_end)
    daniel_free = get_free_intervals(daniel_busy, work_start, work_end)
    
    common_free = intersect_intervals(megan_free, daniel_free)
    
    # Look for a slot that fits the meeting duration
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_day = day
            meeting_start = start
            break
    if meeting_day is not None:
        break

if meeting_day is not None:
    meeting_end = meeting_start + meeting_duration
    # Format output as HH:MM:HH:MM along with day of the week
    print(f"{meeting_day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
else:
    print("No available meeting slot found.")