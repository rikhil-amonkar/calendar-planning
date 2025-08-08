def time_to_minutes(t):
    # Convert time string "HH:MM" to minutes since midnight.
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    # Convert minutes since midnight back to string "HH:MM".
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """
    Given a sorted list of busy intervals (start, end) in minutes,
    compute the free intervals within the work window [work_start, work_end].
    """
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
    """
    Intersect two lists of intervals.
    Each interval is a tuple (start, end) in minutes.
    Returns the intersection intervals.
    """
    intersections = []
    i, j = 0, 0
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            intersections.append((start, end))
        # Advance the pointer that ends earlier.
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return intersections

# Work hours: 09:00 to 17:00.
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # minutes

# Participant busy schedules in minutes.
tyler_schedule = {
    "Monday": [],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("09:30")),
        (time_to_minutes("14:30"), time_to_minutes("15:00"))
    ],
    "Wednesday": [
        (time_to_minutes("10:30"), time_to_minutes("11:00")),
        (time_to_minutes("12:30"), time_to_minutes("13:00")),
        (time_to_minutes("13:30"), time_to_minutes("14:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ]
}

ruth_schedule = {
    "Monday": [
        (time_to_minutes("09:00"), time_to_minutes("10:00")),
        (time_to_minutes("10:30"), time_to_minutes("12:00")),
        (time_to_minutes("12:30"), time_to_minutes("14:30")),
        (time_to_minutes("15:00"), time_to_minutes("16:00")),
        (time_to_minutes("16:30"), time_to_minutes("17:00"))
    ],
    "Tuesday": [
        (time_to_minutes("09:00"), time_to_minutes("17:00"))
    ],
    "Wednesday": [
        (time_to_minutes("09:00"), time_to_minutes("17:00"))
    ]
}

# Tyler's preference: avoid meetings on Monday before 16:00.
def satisfies_constraints(day, interval):
    if day == "Monday":
        # Meeting must start at or after 16:00 (which is 960 minutes).
        return interval[0] >= time_to_minutes("16:00")
    return True

days_to_consider = ["Monday", "Tuesday", "Wednesday"]
proposed_meeting = None
proposed_day = None

for day in days_to_consider:
    # Compute free intervals for both Tyler and Ruth.
    tyler_free = compute_free_intervals(tyler_schedule[day], work_start, work_end)
    ruth_free = compute_free_intervals(ruth_schedule[day], work_start, work_end)
    
    # Find the intersection of free intervals between both.
    common_free = intersect_intervals(tyler_free, ruth_free)
    
    # Look for a free block that fits the duration and any additional constraints.
    for interval in common_free:
        if interval[1] - interval[0] >= meeting_duration and satisfies_constraints(day, interval):
            # If meeting must start after a constraint on Monday, adjust the start time.
            start = interval[0]
            if day == "Monday" and start < time_to_minutes("16:00"):
                start = time_to_minutes("16:00")
            end = start + meeting_duration
            # Ensure the meeting still fits within the interval.
            if end <= interval[1]:
                proposed_meeting = (start, end)
                proposed_day = day
                break
    if proposed_meeting is not None:
        break

if proposed_meeting and proposed_day:
    start_str = minutes_to_time(proposed_meeting[0])
    end_str = minutes_to_time(proposed_meeting[1])
    # Output in the required format: "HH:MM:HH:MM" followed by the day.
    print(f"{start_str}:{end_str} {proposed_day}")
else:
    print("No available meeting time found.")