#!/usr/bin/env python3
def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Working day boundaries (in minutes)
WORK_START = 9 * 60       # 09:00 = 540 minutes
WORK_END = 17 * 60        # 17:00 = 1020 minutes

# Meeting duration in minutes (30 minutes)
MEETING_DURATION = 30

# Roger prefers not to have meetings before 12:30.
ROGER_MIN_START = 12 * 60 + 30  # 12:30 = 750 minutes

# For each participant, we list their busy intervals (start, end) in minutes.
# Note: Times are in minutes from midnight.
busy = {
    "Daniel": [],  # free all day
    "Kathleen": [(14 * 60 + 30, 15 * 60 + 30)],  # 14:30-15:30 -> (870, 930)
    "Carolyn": [(12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30)],  # 12:00-12:30, 13:00-13:30
    "Roger": [],  # no busy meetings, but with extra constraint below
    "Cheryl": [(9 * 60, 9 * 60 + 30), (10 * 60, 11 * 60 + 30),
               (12 * 60 + 30, 13 * 60 + 30), (14 * 60, 17 * 60)],  
               # 9:00-9:30, 10:00-11:30, 12:30-13:30, 14:00-17:00
    "Virginia": [(9 * 60 + 30, 11 * 60 + 30), (12 * 60, 12 * 60 + 30),
                 (13 * 60, 13 * 60 + 30), (14 * 60 + 30, 15 * 60 + 30),
                 (16 * 60, 17 * 60)],  
                 # 9:30-11:30, 12:00-12:30, 13:00-13:30, 14:30-15:30, 16:00-17:00
    "Angela": [(9 * 60 + 30, 10 * 60), (10 * 60 + 30, 11 * 60 + 30),
               (12 * 60, 12 * 60 + 30), (13 * 60, 13 * 60 + 30),
               (14 * 60, 16 * 60 + 30)]  
               # 9:30-10:00, 10:30-11:30, 12:00-12:30, 13:00-13:30, 14:00-16:30
}

# Function to compute free intervals from busy times given the overall work period.
def compute_free_intervals(busy_intervals, work_start, work_end):
    # Sort busy intervals by start time
    busy_intervals = sorted(busy_intervals)
    free = []
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end:
        free.append((current, work_end))
    return free

# Compute free intervals for each participant within working hours.
# Also enforce Roger's preference by adjusting his available start to 12:30.
free = {}
for person, intervals in busy.items():
    person_free = compute_free_intervals(intervals, WORK_START, WORK_END)
    # For Roger, and for our meeting overall, we require start >= 12:30.
    if person == "Roger":
        # Adjust free intervals that start before 12:30
        person_free = [(max(start, ROGER_MIN_START), end) for (start, end) in person_free if end > ROGER_MIN_START]
    free[person] = person_free

# For our meeting, we need a 30-minute slot that is common for everyone.
# We now intersect the free intervals of all participants.
def intersect_intervals(int1, int2):
    """Return the intersection of two lists of intervals."""
    res = []
    i, j = 0, 0
    while i < len(int1) and j < len(int2):
        # Find overlap between int1[i] and int2[j]
        start = max(int1[i][0], int2[j][0])
        end = min(int1[i][1], int2[j][1])
        if start + MEETING_DURATION <= end:
            res.append((start, end))
        # Move to the next interval based on which one finishes first
        if int1[i][1] < int2[j][1]:
            i += 1
        else:
            j += 1
    return res

# Start with the free intervals of the first participant.
participants = list(free.keys())
common_free = free[participants[0]]
for person in participants[1:]:
    common_free = intersect_intervals(common_free, free[person])
    if not common_free:
        break

# Now, from the common free intervals, select the earliest slot that can fit the meeting.
proposed_start = None
for interval in common_free:
    start, end = interval
    if end - start >= MEETING_DURATION:
        proposed_start = start
        break

if proposed_start is not None:
    proposed_end = proposed_start + MEETING_DURATION
    meeting_time = f"{minutes_to_str(proposed_start)}:{minutes_to_str(proposed_end)}"
    day = "Monday"
    print(f"Proposed Meeting Time: {meeting_time} on {day}")
else:
    print("No common meeting time slot found.")