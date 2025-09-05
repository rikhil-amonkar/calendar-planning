def time_to_minutes(t):
    """Convert a HH:MM time string to minutes since midnight."""
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to a HH:MM time string."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Define the meeting duration in minutes
meeting_duration = 30

# Define work hours (in minutes since midnight)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Define busy intervals for each participant (all times in minutes)
busy_intervals = []

# Judy: 13:00-13:30, 16:00-16:30
busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("13:30")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("16:30")))

# Olivia: 10:00-10:30, 12:00-13:00, 14:00-14:30
busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("13:00")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))

# Eric: free all day (no busy intervals)

# Jacqueline: 10:00-10:30, 15:00-15:30
busy_intervals.append((time_to_minutes("10:00"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("15:00"), time_to_minutes("15:30")))

# Laura: 9:00-10:00, 10:30-12:00, 13:00-13:30, 14:30-15:00, 15:30-17:00
busy_intervals.append((time_to_minutes("09:00"), time_to_minutes("10:00")))
busy_intervals.append((time_to_minutes("10:30"), time_to_minutes("12:00")))
busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("13:30")))
busy_intervals.append((time_to_minutes("14:30"), time_to_minutes("15:00")))
busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("17:00")))

# Tyler: 9:00-10:00, 11:00-11:30, 12:30-13:00, 14:00-14:30, 15:30-17:00
busy_intervals.append((time_to_minutes("09:00"), time_to_minutes("10:00")))
busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
busy_intervals.append((time_to_minutes("12:30"), time_to_minutes("13:00")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))
busy_intervals.append((time_to_minutes("15:30"), time_to_minutes("17:00")))

# Lisa: 9:30-10:30, 11:00-11:30, 12:00-12:30, 13:00-13:30, 14:00-14:30, 16:00-17:00
busy_intervals.append((time_to_minutes("09:30"), time_to_minutes("10:30")))
busy_intervals.append((time_to_minutes("11:00"), time_to_minutes("11:30")))
busy_intervals.append((time_to_minutes("12:00"), time_to_minutes("12:30")))
busy_intervals.append((time_to_minutes("13:00"), time_to_minutes("13:30")))
busy_intervals.append((time_to_minutes("14:00"), time_to_minutes("14:30")))
busy_intervals.append((time_to_minutes("16:00"), time_to_minutes("17:00")))

def is_slot_free(start):
    """Check if the meeting slot from start to start+meeting_duration is free for everyone."""
    end = start + meeting_duration
    # For each busy interval, check for an overlap.
    for b_start, b_end in busy_intervals:
        # If the meeting overlaps with a busy interval, return False.
        if start < b_end and end > b_start:
            return False
    return True

# Find the first available slot within work hours
meeting_time_found = False
for candidate in range(work_start, work_end - meeting_duration + 1):
    if is_slot_free(candidate):
        meeting_start = candidate
        meeting_end = candidate + meeting_duration
        meeting_time_found = True
        break

if meeting_time_found:
    meeting_slot = f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}"
    day = "Monday"
    print(f"{day} {meeting_slot}")
else:
    print("No available meeting slot found.")