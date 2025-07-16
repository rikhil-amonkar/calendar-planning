def min_to_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h:02d}:{m:02d}"

# Work hours and day
work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020
meeting_duration = 30
preference_cutoff = 13 * 60  # 780 (1 PM)

# Busy intervals for each participant in minutes (each as (start, end))
# Christine
christine_busy = [
    (9*60+30, 10*60+30),
    (12*60, 12*60+30),
    (13*60, 13*60+30),
    (14*60+30, 15*60),
    (16*60, 16*60+30)
]
# Janice: none
janice_busy = []
# Bobby
bobby_busy = [
    (12*60, 12*60+30),
    (14*60+30, 15*60)
]
# Elizabeth
elizabeth_busy = [
    (9*60, 9*60+30),
    (11*60+30, 13*60),
    (13*60+30, 14*60),
    (15*60, 15*60+30),
    (16*60, 17*60)
]
# Tyler
tyler_busy = [
    (9*60, 11*60),
    (12*60, 12*60+30),
    (13*60, 13*60+30),
    (15*60+30, 16*60),
    (16*60+30, 17*60)
]
# Edward
edward_busy = [
    (9*60, 9*60+30),
    (10*60, 11*60),
    (11*60+30, 14*60),
    (14*60+30, 15*60+30),
    (16*60, 17*60)
]

# Combine all busy intervals
all_busy = []
all_busy.extend(christine_busy)
all_busy.extend(janice_busy)
all_busy.extend(bobby_busy)
all_busy.extend(elizabeth_busy)
all_busy.extend(tyler_busy)
all_busy.extend(edward_busy)

# Sort by start time
all_busy.sort(key=lambda x: x[0])

# Merge intervals
merged_busy = []
if all_busy:
    merged_busy = [all_busy[0]]
    for i in range(1, len(all_busy)):
        current = all_busy[i]
        last = merged_busy[-1]
        if current[0] <= last[1]:
            if current[1] > last[1]:
                merged_busy[-1] = (last[0], current[1])
        else:
            merged_busy.append(current)

# Now compute free intervals
free_intervals = []
current_start = work_start
for busy in merged_busy:
    if busy[0] > current_start:
        free_intervals.append((current_start, busy[0]))
    current_start = max(current_start, busy[1])
if current_start < work_end:
    free_intervals.append((current_start, work_end))

# Now, look for a meeting slot
meeting_slot = None
# First, try to find a slot that ends by preference_cutoff (780)
for interval in free_intervals:
    start, end = interval
    if end - start >= meeting_duration:
        if start + meeting_duration <= preference_cutoff:
            meeting_slot = (start, start + meeting_duration)
            break

if meeting_slot is None:
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

# Convert meeting_slot to time string
if meeting_slot is not None:
    day = "Monday"
    start_time_str = min_to_time(meeting_slot[0])
    end_time_str = min_to_time(meeting_slot[1])
    time_range_str = f"{start_time_str}:{end_time_str}"
    print(f"{day} {time_range_str}")