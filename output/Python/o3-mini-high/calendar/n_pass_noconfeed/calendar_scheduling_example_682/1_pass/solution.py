def time_to_minutes(time_str):
    """Convert HH:MM string to minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes from midnight back to HH:MM string."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy_intervals, work_start, work_end):
    """Given busy intervals (in minutes) and a work window,
    return a list of free intervals within that window."""
    free = []
    current = work_start
    for start, end in sorted(busy_intervals):
        if current < start:
            free.append((current, start))
        if current < end:
            current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

def find_slot_in_free_intervals(free_intervals, duration):
    """Return the first slot of at least 'duration' minutes."""
    for start, end in free_intervals:
        if end - start >= duration:
            return start, start + duration
    return None

def merge_intervals(intervals):
    """Merge overlapping intervals. Each interval is a tuple (start, end)."""
    merged = []
    for interval in sorted(intervals, key=lambda x: x[0]):
        if not merged:
            merged.append(interval)
        else:
            last_start, last_end = merged[-1]
            current_start, current_end = interval
            if current_start <= last_end:  # overlap
                merged[-1] = (last_start, max(last_end, current_end))
            else:
                merged.append(interval)
    return merged

# Meeting parameters
meeting_duration = 30  # in minutes

# Work hours: 09:00 to 17:00 is general, but due to Amanda's Tuesday constraint, we limit Tuesday to 09:00 to 11:00.
work_start_str = "09:00"
work_end_str = "11:00"  # Because Amanda doesn't want Tuesday meetings after 11:00
work_start = time_to_minutes(work_start_str)
work_end = time_to_minutes(work_end_str)

# Busy schedules in HH:MM format for Tuesday (only intervals affecting the work window are relevant)
# Amanda's busy times on Tuesday and her "no after 11:00" constraint
amanda_busy_times = [
    ("09:00", "09:30"),
    ("10:00", "10:30"),
    # Other intervals are after 11:00 or outside our limited window, so we ignore them.
]

# Nathan's busy times on Tuesday
nathan_busy_times = [
    ("09:00", "10:30"),
    # Other intervals either start at 11:00 (which is our end) or later.
]

# Convert busy times to minutes and restrict to the meeting window [work_start, work_end]
amanda_busy = []
for start, end in amanda_busy_times:
    s = time_to_minutes(start)
    e = min(time_to_minutes(end), work_end)
    if s < work_end:
        amanda_busy.append((s, e))

nathan_busy = []
for start, end in nathan_busy_times:
    s = time_to_minutes(start)
    e = min(time_to_minutes(end), work_end)
    if s < work_end:
        nathan_busy.append((s, e))

# Combine busy intervals from both participants for Tuesday.
combined_busy = amanda_busy + nathan_busy
merged_busy = merge_intervals(combined_busy)

# Compute free intervals from 09:00 to 11:00 for Tuesday based on the merged busy time.
free_intervals = compute_free_intervals(merged_busy, work_start, work_end)

# Find a free slot that fits the meeting duration.
slot = find_slot_in_free_intervals(free_intervals, meeting_duration)

if slot:
    start_str = minutes_to_time(slot[0])
    end_str = minutes_to_time(slot[1])
    # Output in the format: Day HH:MM:HH:MM
    print(f"Tuesday {start_str}:{end_str}")
else:
    print("No available meeting slot found.")