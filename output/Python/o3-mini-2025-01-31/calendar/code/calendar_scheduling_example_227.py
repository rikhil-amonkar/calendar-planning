def minutes_to_hhmm(minutes):
    hh = minutes // 60
    mm = minutes % 60
    return f"{hh:02d}:{mm:02d}"

# Define meeting parameters
meeting_duration = 30  # in minutes
day = "Monday"
# Work hours in minutes since midnight: 9:00 - 17:00
work_start = 9 * 60
work_end = 17 * 60

# Earliest meeting start constraint from David: not before 14:00
constraint_start = 14 * 60

# Define each participant's busy times (in minutes since midnight)
# Format: (start, end)
busy_times = {
    "Natalie": [],
    "David": [(11 * 60 + 30, 12 * 60 + 0), (14 * 60 + 30, 15 * 60 + 0)],
    "Douglas": [(9 * 60 + 30, 10 * 60 + 0), (11 * 60 + 30, 12 * 60 + 0),
                (13 * 60 + 0, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 0)],
    "Ralph": [(9 * 60 + 0, 9 * 60 + 30), (10 * 60 + 0, 11 * 60 + 0),
              (11 * 60 + 30, 12 * 60 + 30), (13 * 60 + 30, 15 * 60 + 0),
              (15 * 60 + 30, 16 * 60 + 0), (16 * 60 + 30, 17 * 60 + 0)],
    "Jordan": [(9 * 60 + 0, 10 * 60 + 0), (12 * 60 + 0, 12 * 60 + 30),
               (13 * 60 + 0, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 0),
               (15 * 60 + 30, 17 * 60 + 0)]
}

# We'll combine all busy intervals and consider only the parts within the meeting window.
all_busy = []
for person, intervals in busy_times.items():
    for start, end in intervals:
        # Only consider intervals that overlap with our working window (and David's constraint)
        if end > constraint_start and start < work_end:
            # Clamp each busy interval to the window [constraint_start, work_end]
            clamped_start = max(start, constraint_start)
            clamped_end = min(end, work_end)
            all_busy.append((clamped_start, clamped_end))

# Sort intervals by start time
all_busy.sort()

# Merge overlapping busy intervals
merged_busy = []
for interval in all_busy:
    if not merged_busy:
        merged_busy.append(interval)
    else:
        last_start, last_end = merged_busy[-1]
        curr_start, curr_end = interval
        if curr_start <= last_end:  # overlapping
            merged_busy[-1] = (last_start, max(last_end, curr_end))
        else:
            merged_busy.append(interval)

# Now find free intervals in the window from constraint_start to work_end,
# by checking gaps between merged busy times.
free_intervals = []
current_start = constraint_start
for busy_start, busy_end in merged_busy:
    if current_start < busy_start:
        free_intervals.append((current_start, busy_start))
    current_start = max(current_start, busy_end)
if current_start < work_end:
    free_intervals.append((current_start, work_end))

# Find the first free interval that can fit the meeting_duration
proposed_time = None
for free_start, free_end in free_intervals:
    if free_end - free_start >= meeting_duration:
        proposed_time = (free_start, free_start + meeting_duration)
        break

if proposed_time:
    start_time, end_time = proposed_time
    print(f"{day} {minutes_to_hhmm(start_time)}:{minutes_to_hhmm(end_time)}")
else:
    print("No suitable time slot available.")