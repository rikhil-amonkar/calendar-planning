def minutes_to_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

meeting_duration = 30  # duration in minutes

# Working day Tuesday: 09:00 to 17:00 in minutes
work_start = 9 * 60      # 540 minutes
work_end = 17 * 60       # 1020 minutes

# Margaret's Tuesday busy intervals (in minutes)
# 12:00 to 12:30 is busy -> 720 to 750
margaret_busy = [(720, 750)]
# Margaret's initial free intervals (within working hours)
margaret_free = []
if work_start < margaret_busy[0][0]:
    margaret_free.append((work_start, margaret_busy[0][0]))
if margaret_busy[0][1] < work_end:
    margaret_free.append((margaret_busy[0][1], work_end))

# Margaret prefers NOT to meet before 14:30 (870 minutes).
# So we adjust her free intervals to only consider times on or after 14:30.
margaret_effective_free = []
for start, end in margaret_free:
    if end <= 870:
        continue  # interval ends before 14:30, so skip
    effective_start = max(start, 870)
    if effective_start < end:
        margaret_effective_free.append((effective_start, end))
        
# Alexis's Tuesday busy intervals (in minutes)
# 09:00 to 09:30, 10:00 to 10:30, and 14:00 to 16:30
alexis_busy = [(9 * 60, 9 * 60 + 30), (10 * 60, 10 * 60 + 30), (14 * 60, 16 * 60 + 30)]
alexis_busy.sort()

# Calculate Alexis's free intervals within working hours by taking the complement of her busy times.
alexis_free = []
current = work_start
for b_start, b_end in alexis_busy:
    if current < b_start:
        alexis_free.append((current, b_start))
    current = max(current, b_end)
if current < work_end:
    alexis_free.append((current, work_end))

# Function to compute the intersection between two intervals.
def interval_intersection(interval1, interval2):
    start = max(interval1[0], interval2[0])
    end = min(interval1[1], interval2[1])
    if start < end:
        return (start, end)
    return None

# Find possible meeting slots that satisfy a 30-minute meeting.
possible_slots = []
for m_interval in margaret_effective_free:
    for a_interval in alexis_free:
        inter = interval_intersection(m_interval, a_interval)
        if inter and (inter[1] - inter[0] >= meeting_duration):
            possible_slots.append(inter)

# Since the problem assures a solution exists, select the earliest slot.
if possible_slots:
    slot = possible_slots[0]
    meeting_start = slot[0]
    meeting_end = meeting_start + meeting_duration
    # Format time range as HH:MM:HH:MM
    time_range_str = f"{minutes_to_str(meeting_start)}:{minutes_to_str(meeting_end)}"
    day = "Tuesday"
    print(day, time_range_str)
else:
    print("No suitable meeting slot found.")