def minutes_to_str(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define working hours in minutes since 00:00 (9:00 to 17:00)
work_start = 9 * 60   # 540
work_end = 17 * 60    # 1020

# Meeting duration in minutes
duration = 60

# Constraint: Mark prefers meetings not before 15:00, so earliest start is 15:00
earliest_start = 15 * 60  # 900

# Define busy intervals in minutes for each participant
# Stephanie busy: 9:00-9:30 (540-570) and 13:30-14:00 (810-840)
stephanie_busy = [(540, 570), (810, 840)]
# Scott busy: 9:00-10:00 (540-600), 11:00-12:30 (660-750), 14:30-15:00 (870-900), 16:00-17:00 (960-1020)
scott_busy = [(540, 600), (660, 750), (870, 900), (960, 1020)]
# Mark is free the entire day but prefers meeting after 15:00.

def is_free(start, end, busy_intervals):
    """Return True if interval [start, end] does not overlap any busy interval."""
    for b_start, b_end in busy_intervals:
        # Check if [start, end] overlaps with busy interval
        if not (end <= b_start or start >= b_end):
            return False
    return True

# Starting from earliest possible start, try to schedule the meeting at the earliest availability.
# Given the problem guarantees a solution, we'll check the candidate time.
candidate_start = earliest_start
candidate_end = candidate_start + duration

# Check that candidate falls within working hours
if candidate_end > work_end:
    raise ValueError("Candidate meeting time exceeds working hours.")

# Check if candidate time is free for Stephanie and Scott
if is_free(candidate_start, candidate_end, stephanie_busy) and is_free(candidate_start, candidate_end, scott_busy):
    proposed_start = candidate_start
    proposed_end = candidate_start + duration
    # Output in the required format: {HH:MM:HH:MM}
    print("{" + minutes_to_str(proposed_start) + ":" + minutes_to_str(proposed_end) + "}")
else:
    # If the candidate does not work, then search minute-by-minute until an available slot is found.
    found = False
    for t in range(candidate_start + 1, work_end - duration + 1):
        if is_free(t, t+duration, stephanie_busy) and is_free(t, t+duration, scott_busy):
            proposed_start = t
            proposed_end = t + duration
            print("{" + minutes_to_str(proposed_start) + ":" + minutes_to_str(proposed_end) + "}")
            found = True
            break
    if not found:
        print("No available time")

