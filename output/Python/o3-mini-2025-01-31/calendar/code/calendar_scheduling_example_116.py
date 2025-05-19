def time_to_minutes(t):
    """Convert 'HH:MM' string to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to 'HH:MM' string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def subtract_busy(working, busy_times):
    """
    Given a working interval (start, end) and a list of busy intervals (each a tuple),
    return a list of free intervals (as tuples) within the working period.
    Assumes busy_times are sorted and non overlapping.
    """
    free = []
    current_start = working[0]
    for bstart, bend in busy_times:
        if bstart > current_start:
            free.append((current_start, bstart))
        current_start = max(current_start, bend)
    if current_start < working[1]:
        free.append((current_start, working[1]))
    return free

def intersect_intervals(list1, list2):
    """Intersect two lists of intervals and return the overlapping intervals."""
    i, j = 0, 0
    result = []
    while i < len(list1) and j < len(list2):
        start1, end1 = list1[i]
        start2, end2 = list2[j]
        # Find overlap
        start_overlap = max(start1, start2)
        end_overlap = min(end1, end2)
        if start_overlap < end_overlap:
            result.append((start_overlap, end_overlap))
        # Move the pointer that ends earlier
        if end1 < end2:
            i += 1
        else:
            j += 1
    return result

# Define working hours in minutes (9:00-17:00)
working = (time_to_minutes("09:00"), time_to_minutes("17:00"))

# Busy schedules (all times in minutes) for each participant on Monday:
# Adam busy: 14:00-15:00
adam_busy = [(time_to_minutes("14:00"), time_to_minutes("15:00"))]

# John busy: 13:00-13:30, 14:00-14:30, 15:30-16:00, 16:30-17:00
john_busy = [
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("14:00"), time_to_minutes("14:30")),
    (time_to_minutes("15:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Stephanie busy: 9:30-10:00, 10:30-11:00, 11:30-16:00, 16:30-17:00
stephanie_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Anna busy: 9:30-10:00, 12:00-12:30, 13:00-15:30, 16:30-17:00
anna_busy = [
    (time_to_minutes("09:30"), time_to_minutes("10:00")),
    (time_to_minutes("12:00"), time_to_minutes("12:30")),
    (time_to_minutes("13:00"), time_to_minutes("15:30")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Compute free intervals for each participant
adam_free = subtract_busy(working, adam_busy)
john_free = subtract_busy(working, john_busy)
stephanie_free = subtract_busy(working, stephanie_busy)
anna_free = subtract_busy(working, anna_busy)

# Anna prefers not to meet before 14:30. Adjust her free intervals accordingly.
pref_start = time_to_minutes("14:30")
adjusted_anna_free = []
for start, end in anna_free:
    # If the interval ends before the preference start, skip it.
    if end <= pref_start:
        continue
    # Adjust the start if needed.
    adjusted_anna_free.append((max(start, pref_start), end))
anna_free = adjusted_anna_free

# Calculate the intersection of all participants' free intervals
all_free = intersect_intervals(adam_free, john_free)
all_free = intersect_intervals(all_free, stephanie_free)
all_free = intersect_intervals(all_free, anna_free)

# Meeting duration: 30 minutes
meeting_duration = 30

# Find an interval that can accommodate the meeting duration
proposed_interval = None
for start, end in all_free:
    if end - start >= meeting_duration:
        proposed_interval = (start, start + meeting_duration)
        break

if proposed_interval:
    start_str = minutes_to_time(proposed_interval[0])
    end_str = minutes_to_time(proposed_interval[1])
    # Day of the week is Monday
    print(f"Monday {start_str}:{end_str}")
else:
    print("No available meeting time found.")