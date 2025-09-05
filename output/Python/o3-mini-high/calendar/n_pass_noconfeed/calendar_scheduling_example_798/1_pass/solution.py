def time_to_minutes(t):
    """Convert HH:MM time string to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to HH:MM time string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def get_free_intervals(blocks, work_start, work_end):
    """
    Given a list of busy intervals (as tuples of minutes) and working
    start/end times, return a list of free intervals.
    """
    free = []
    current = work_start
    # Sort blocks by start time
    for start, end in sorted(blocks, key=lambda b: b[0]):
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def intersect_intervals(intervals1, intervals2):
    """
    Given two lists of intervals, compute their intersection.
    Each interval is a tuple (start, end).
    """
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        # Move to the next interval in the list which ends first.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Meeting duration in minutes
meeting_duration = 30

# Define working hours (9:00 to 17:00)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Schedules for Nancy (busy intervals) by day
nancy_schedule = {
    "Monday": [("10:00", "10:30"), ("11:30", "12:30"), ("13:30", "14:00"),
               ("14:30", "15:30"), ("16:00", "17:00")],
    "Tuesday": [("9:30", "10:30"), ("11:00", "11:30"), ("12:00", "12:30"),
                ("13:00", "13:30"), ("15:30", "16:00")],
    "Wednesday": [("10:00", "11:30"), ("13:30", "16:00")]
}

# Schedules for Jose (busy intervals) by day
jose_schedule = {
    "Monday": [("9:00", "17:00")],
    "Tuesday": [("9:00", "17:00")],
    "Wednesday": [("9:00", "9:30"), ("10:00", "12:30"),
                  ("13:30", "14:30"), ("15:00", "17:00")]
}

# Convert the schedule times to minutes
for day, intervals in nancy_schedule.items():
    nancy_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

for day, intervals in jose_schedule.items():
    jose_schedule[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in intervals]

# Try to find the earliest available meeting slot in day order.
days_order = ["Monday", "Tuesday", "Wednesday"]
meeting_found = False

for day in days_order:
    # If any participant has no schedule info for the day, assume they're free for the day.
    nancy_blocks = nancy_schedule.get(day, [])
    jose_blocks = jose_schedule.get(day, [])
    
    # Compute free intervals during work hours for each participant.
    nancy_free = get_free_intervals(nancy_blocks, work_start, work_end)
    jose_free = get_free_intervals(jose_blocks, work_start, work_end)
    
    # Find intersections of free intervals.
    common_free = intersect_intervals(nancy_free, jose_free)
    
    # Check each intersection for enough duration.
    for start, end in common_free:
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = meeting_start + meeting_duration
            # Output in the required format: day and HH:MM:HH:MM time range
            print(f"{day} {minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            meeting_found = True
            break
    if meeting_found:
        break

if not meeting_found:
    print("No available slot found.")