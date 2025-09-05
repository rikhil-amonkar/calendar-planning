def time_to_minutes(t):
    """Convert time string 'HH:MM' to minutes since midnight."""
    hours, minutes = map(int, t.split(":"))
    return hours * 60 + minutes

def minutes_to_time(m):
    """Convert minutes since midnight to time string 'HH:MM'."""
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

def is_slot_free(busy_intervals, start, end):
    """
    Returns True if the meeting [start, end) does not conflict with any busy interval.
    A conflict exists if the meeting overlaps a busy slot.
    """
    for b_start, b_end in busy_intervals:
        # If meeting start < busy end and meeting end > busy start, there's an overlap.
        if start < b_end and end > b_start:
            return False
    return True

# Define work day parameters (Monday)
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")
meeting_duration = 30  # in minutes
day = "Monday"

# Busy intervals for each participant in minutes since midnight.
# Each tuple is (start, end), where times are in minutes.
schedules = {
    "Shirley": [(time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("12:00"), time_to_minutes("12:30"))],
    "Jacob":   [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                (time_to_minutes("10:00"), time_to_minutes("10:30")),
                (time_to_minutes("11:00"), time_to_minutes("11:30")),
                (time_to_minutes("12:30"), time_to_minutes("13:30")),
                (time_to_minutes("14:30"), time_to_minutes("15:00"))],
    "Stephen": [(time_to_minutes("11:30"), time_to_minutes("12:00")),
                (time_to_minutes("12:30"), time_to_minutes("13:00"))],
    "Margaret": [(time_to_minutes("09:00"), time_to_minutes("09:30")),
                 (time_to_minutes("10:30"), time_to_minutes("12:30")),
                 (time_to_minutes("13:00"), time_to_minutes("13:30")),
                 (time_to_minutes("15:00"), time_to_minutes("15:30")),
                 (time_to_minutes("16:30"), time_to_minutes("17:00"))],
    "Mason":   [(time_to_minutes("09:00"), time_to_minutes("10:00")),
                (time_to_minutes("10:30"), time_to_minutes("11:00")),
                (time_to_minutes("11:30"), time_to_minutes("12:30")),
                (time_to_minutes("13:00"), time_to_minutes("13:30")),
                (time_to_minutes("14:00"), time_to_minutes("14:30")),
                (time_to_minutes("16:30"), time_to_minutes("17:00"))]
}

# Additional constraint: Margaret does not want to meet before 14:30 on Monday.
margaret_earliest = time_to_minutes("14:30")

# Because of Margaret's constraint, the meeting start must be no earlier than 14:30.
candidate_start_min = max(work_start, margaret_earliest)
candidate_start_max = work_end - meeting_duration

# List of participants
participants = ["Shirley", "Jacob", "Stephen", "Margaret", "Mason"]

proposed_start = None

# Iterate over candidate start times (in minutes) to find the earliest valid slot.
for start in range(candidate_start_min, candidate_start_max + 1):
    end = start + meeting_duration
    valid = True
    for person in participants:
        # For Margaret, enforce meeting start is not before 14:30.
        if person == "Margaret" and start < margaret_earliest:
            valid = False
            break

        if not is_slot_free(schedules[person], start, end):
            valid = False
            break
    if valid:
        proposed_start = start
        proposed_end = end
        break

if proposed_start is not None:
    # Format the time as HH:MM:HH:MM and include the day of the week.
    meeting_time = f"{minutes_to_time(proposed_start)}:{minutes_to_time(proposed_end)}"
    print(f"{day} {meeting_time}")
else:
    print("No available slot found.")