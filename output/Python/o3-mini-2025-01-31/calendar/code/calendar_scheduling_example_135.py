from datetime import time, datetime

def time_to_minutes(t):
    return t.hour * 60 + t.minute

def minutes_to_time_str(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Define meeting day and duration in minutes.
day = "Monday"
meeting_duration = 30

# Define free intervals for each participant (in minutes from 0:00)
# Work hours: 9:00 - 17:00 => 540 - 1020 minutes
# Eric: free all day --> [540, 1020]
eric_free = [(540, 1020)]

# Ashley's busy intervals: 10:00-10:30, 11:00-12:00, 12:30-13:00, 15:00-16:00
# So her free intervals within work hours:
ashley_free = [(540, 600),    # 9:00-10:00
               (630, 660),    # 10:30-11:00
               (720, 750),    # 12:00-12:30
               (780, 900),    # 13:00-15:00
               (960, 1020)]   # 16:00-17:00

# Ronald's busy intervals: 9:00-9:30, 10:00-11:30, 12:30-14:00, 14:30-17:00
ronald_free = [(570, 600),    # 9:30-10:00
               (690, 750),    # 11:30-12:30
               (840, 870)]    # 14:00-14:30

# Larry's busy intervals: 9:00-12:00, 13:00-17:00
larry_free = [(720, 780)]     # 12:00-13:00

def intersect_intervals(intervals1, intervals2):
    """Intersect two lists of intervals."""
    result = []
    for start1, end1 in intervals1:
        for start2, end2 in intervals2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start >= meeting_duration:
                result.append((start, end))
    return result

# Compute the intersection of all free intervals
common_free = eric_free
for free in [ashley_free, ronald_free, larry_free]:
    common_free = intersect_intervals(common_free, free)

# From the intersected free intervals, choose the earliest slot that can accommodate the meeting.
meeting_start = None
for start, end in common_free:
    if end - start >= meeting_duration:
        meeting_start = start
        break

if meeting_start is not None:
    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time_str(meeting_start)
    end_str = minutes_to_time_str(meeting_end)
    # Output in the required format HH:MM:HH:MM along with day
    print(f"{day} {start_str}:{end_str}")
else:
    print("No available time slot found.")