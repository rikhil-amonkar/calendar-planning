from datetime import timedelta, datetime

def time_to_minutes(t):
    """Converts HH:MM string to minutes since midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def minutes_to_time(m):
    """Converts minutes since midnight to HH:MM string."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def intervals_free(busy, work_start, work_end):
    """
    Given busy intervals (list of (start, end) in minutes), 
    returns free intervals between work_start and work_end.
    """
    free = []
    current = work_start
    for bstart, bend in sorted(busy):
        if current < bstart:
            free.append((current, bstart))
        current = max(current, bend)
    if current < work_end:
        free.append((current, work_end))
    return free

def overlaps(slot, busy_interval):
    """Returns True if slot [start, end) overlaps busy_interval."""
    s, e = slot
    bstart, bend = busy_interval
    # Overlap exists if the slot and busy interval are not completely separate
    return not (e <= bstart or s >= bend)

def is_slot_free(slot, busy):
    """Check if the given slot (in minutes) is free from all busy intervals."""
    for b in busy:
        if overlaps(slot, b):
            return False
    return True

# Define work hours for Monday (in minutes)
# Monday workday is 09:00 to 17:00.
work_start = time_to_minutes("09:00")
work_end   = time_to_minutes("17:00")

# Meeting duration: 30 minutes
meeting_duration = 30

# Busy schedules for each participant on Monday (times in minutes from midnight)
margaret_busy = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("11:30"), time_to_minutes("12:00")),
    (time_to_minutes("13:00"), time_to_minutes("13:30")),
    (time_to_minutes("15:00"), time_to_minutes("15:30"))
]

donna_busy = [
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("16:00"), time_to_minutes("16:30"))
]

helen_busy = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("11:30")),
    (time_to_minutes("13:00"), time_to_minutes("14:00")),
    (time_to_minutes("14:30"), time_to_minutes("15:00")),
    (time_to_minutes("15:30"), time_to_minutes("17:00"))
]

# Helen's additional constraint: do not meet after 13:30.
# So, the meeting must end by 13:30; hence the latest start is 13:00.
latest_start_for_helen = time_to_minutes("13:00")

# We'll search for an available starting time between work_start and latest_start_for_helen.
# Check minute by minute.
candidate = None
for start in range(work_start, latest_start_for_helen + 1):
    end = start + meeting_duration
    # If the meeting runs past the work_end, break (shouldn't happen on Monday mornings)
    if end > work_end:
        break
    # Meeting must end by 13:30 for Helen
    if end > time_to_minutes("13:30"):
        continue

    slot = (start, end)
    # Check if slot is free for everyone
    if (is_slot_free(slot, margaret_busy) and 
        is_slot_free(slot, donna_busy) and 
        is_slot_free(slot, helen_busy)):
        candidate = slot
        break

if candidate:
    start_time = minutes_to_time(candidate[0])
    end_time   = minutes_to_time(candidate[1])
    # Output in the format HH:MM:HH:MM and include the day of the week.
    print(f"{start_time}:{end_time} Monday")
else:
    print("No available slot found")