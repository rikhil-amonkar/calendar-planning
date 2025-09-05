def time_to_minutes(t):
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    # Ensure busy intervals are sorted by start time
    busy_intervals.sort(key=lambda x: x[0])
    free_intervals = []
    prev_end = work_start
    for start, end in busy_intervals:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        # Update previous end time if needed
        if end > prev_end:
            prev_end = end
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))
    return free_intervals

def intersect_intervals(intervals1, intervals2):
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start1, end1 = intervals1[i]
        start2, end2 = intervals2[j]
        # Find overlapping segment
        start = max(start1, start2)
        end = min(end1, end2)
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list that ends first
        if end1 < end2:
            i += 1
        else:
            j += 1
    return intersections

# Busy schedules for Susan and Sandra as provided
susan_schedule = {
    "Monday": [("12:30", "13:00"), ("13:30", "14:00")],
    "Tuesday": [("11:30", "12:00")],
    "Wednesday": [("09:30", "10:30"), ("14:00", "14:30"), ("15:30", "16:30")]
}

sandra_schedule = {
    "Monday": [("09:00", "13:00"), ("14:00", "15:00"), ("16:00", "16:30")],
    "Tuesday": [("09:00", "09:30"), ("10:30", "12:00"), ("12:30", "13:30"),
                ("14:00", "14:30"), ("16:00", "17:00")],
    "Wednesday": [("09:00", "11:30"), ("12:00", "12:30"), ("13:00", "17:00")]
}

# Convert schedule times to minutes for easier calculation
for day, intervals in susan_schedule.items():
    susan_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

for day, intervals in sandra_schedule.items():
    sandra_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

meeting_duration = 30  # Duration in minutes

# Define working hours (09:00 to 17:00)
WORK_START = time_to_minutes("09:00")
WORK_END = time_to_minutes("17:00")
# Special constraint for Sandra on Monday (she cannot meet after 16:00)
SANDRA_MONDAY_END = time_to_minutes("16:00")

# Candidate days: Susan prefers not to meet on Tuesday, so try Monday and Wednesday first.
candidate_days = ["Monday", "Wednesday", "Tuesday"]

meeting_found = False

for day in candidate_days:
    # Susan works full hours 09:00-17:00 every day.
    susan_work_start = WORK_START
    susan_work_end = WORK_END

    # Sandra's working hours on Monday are restricted by her constraint.
    if day == "Monday":
        sandra_work_start = WORK_START
        sandra_work_end = SANDRA_MONDAY_END
    else:
        sandra_work_start = WORK_START
        sandra_work_end = WORK_END

    # Get busy intervals for the day; if no meetings, use empty list.
    susan_busy = susan_schedule.get(day, [])
    sandra_busy = sandra_schedule.get(day, [])

    # Calculate free intervals during the working hours for both participants.
    susan_free = get_free_intervals(susan_busy, susan_work_start, susan_work_end)
    sandra_free = get_free_intervals(sandra_busy, sandra_work_start, sandra_work_end)

    # Find intersection of free intervals.
    common_free = intersect_intervals(susan_free, sandra_free)

    # Look for the earliest common free slot that fits the meeting duration.
    meeting_slot = None
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    if meeting_slot:
        meeting_found = True
        meeting_day = day
        meeting_start, meeting_end = meeting_slot
        break

if meeting_found:
    # Output the meeting time in the requested format: HH:MM:HH:MM plus the day of the week.
    print(f"{meeting_day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
else:
    print("No available meeting slot found.")