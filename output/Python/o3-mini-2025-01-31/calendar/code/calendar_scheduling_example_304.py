def str_to_minutes(time_str):
    """Convert HH:MM string to minutes from midnight."""
    hours, minutes = map(int, time_str.split(":"))
    return hours * 60 + minutes

def minutes_to_str(minutes):
    """Convert minutes from midnight to HH:MM format."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def overlaps(start1, end1, start2, end2):
    """Return True if [start1, end1) overlaps with [start2, end2)."""
    return max(start1, start2) < min(end1, end2)

# Define the meeting duration in minutes
meeting_duration = 30

# Working hours for the day are normally 9:00 to 17:00,
# but Janice prefers not to meet after 13:00 on Monday.
# Therefore, we limit the search window to 9:00 to 13:00.
work_start = str_to_minutes("09:00")
work_end   = str_to_minutes("13:00")

# Busy intervals for each participant on Monday.
# Times are given as (start, end) in minutes from midnight.
busy = {
    "Christine": [(str_to_minutes("09:30"), str_to_minutes("10:30")),
                  (str_to_minutes("12:00"), str_to_minutes("12:30")),
                  (str_to_minutes("13:00"), str_to_minutes("13:30")),
                  (str_to_minutes("14:30"), str_to_minutes("15:00")),
                  (str_to_minutes("16:00"), str_to_minutes("16:30"))],
    "Janice":    [],  # entire day free.
    "Bobby":     [(str_to_minutes("12:00"), str_to_minutes("12:30")),
                  (str_to_minutes("14:30"), str_to_minutes("15:00"))],
    "Elizabeth": [(str_to_minutes("09:00"), str_to_minutes("09:30")),
                  (str_to_minutes("11:30"), str_to_minutes("13:00")),
                  (str_to_minutes("13:30"), str_to_minutes("14:00")),
                  (str_to_minutes("15:00"), str_to_minutes("15:30")),
                  (str_to_minutes("16:00"), str_to_minutes("17:00"))],
    "Tyler":     [(str_to_minutes("09:00"), str_to_minutes("11:00")),
                  (str_to_minutes("12:00"), str_to_minutes("12:30")),
                  (str_to_minutes("13:00"), str_to_minutes("13:30")),
                  (str_to_minutes("15:30"), str_to_minutes("16:00")),
                  (str_to_minutes("16:30"), str_to_minutes("17:00"))],
    "Edward":    [(str_to_minutes("09:00"), str_to_minutes("09:30")),
                  (str_to_minutes("10:00"), str_to_minutes("11:00")),
                  (str_to_minutes("11:30"), str_to_minutes("14:00")),
                  (str_to_minutes("14:30"), str_to_minutes("15:30")),
                  (str_to_minutes("16:00"), str_to_minutes("17:00"))],
}

# Function to check if a meeting starting at 'start' and ending at 'end'
# conflicts with any busy interval in a given schedule.
def is_available(start, end, busy_intervals):
    for b_start, b_end in busy_intervals:
        # Only consider busy intervals that fall within our search window.
        # We check for overlap with the meeting time.
        if overlaps(start, end, b_start, b_end):
            return False
    return True

meeting_found = False
proposed_start = None

# Iterate over all possible start times (in minutes) from work_start up to work_end - meeting_duration.
for start in range(work_start, work_end - meeting_duration + 1):
    end = start + meeting_duration
    # Assume meeting slot is valid unless one participant is busy.
    slot_valid = True
    for person, busy_intervals in busy.items():
        if not is_available(start, end, busy_intervals):
            slot_valid = False
            break
    if slot_valid:
        proposed_start = start
        meeting_found = True
        break

if meeting_found:
    proposed_end = proposed_start + meeting_duration
    meeting_time_str = f"{minutes_to_str(proposed_start)}:{minutes_to_str(proposed_end)}"
    day_of_week = "Monday"
    print(f"{day_of_week} {meeting_time_str}")
else:
    print("No available meeting slot found.")