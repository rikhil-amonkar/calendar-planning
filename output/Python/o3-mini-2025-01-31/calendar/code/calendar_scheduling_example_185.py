from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Converts a time string 'HH:MM' to minutes after midnight."""
    t = datetime.strptime(time_str, "%H:%M")
    return t.hour * 60 + t.minute

def minutes_to_time(minutes):
    """Converts minutes after midnight to a time string 'HH:MM'."""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Define the workday boundaries
work_start = time_to_minutes("09:00")
work_end = time_to_minutes("17:00")

# Meeting duration in minutes
meeting_duration = 30

# Free intervals for each participant are defined in minutes after midnight.
# Kimberly's free intervals on Monday (excluding her meetings)
kimberly_free = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("10:30"), time_to_minutes("11:00")),
    (time_to_minutes("12:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Megan is free all day, but prefers to avoid meetings before 10:00.
# So we consider her free time starting at 10:00.
megan_free = [
    (time_to_minutes("10:00"), time_to_minutes("17:00"))
]

# Marie's free intervals on Monday (complement of her meetings)
marie_free = [
    (time_to_minutes("09:00"), time_to_minutes("10:00")),
    (time_to_minutes("11:00"), time_to_minutes("11:30")),
    (time_to_minutes("15:00"), time_to_minutes("16:00")),
    (time_to_minutes("16:30"), time_to_minutes("17:00"))
]

# Diana's free intervals on Monday (complement of her meetings)
diana_free = [
    (time_to_minutes("09:00"), time_to_minutes("09:30")),
    (time_to_minutes("10:00"), time_to_minutes("10:30")),
    (time_to_minutes("14:30"), time_to_minutes("15:30"))
]

# Function to find common available slot among participants
def find_common_slot(free_times_lists, duration):
    """
    Given a list of lists containing free intervals for each participant and the meeting duration,
    find a common interval that satisfies the duration.
    Each free interval is a tuple (start, end) in minutes.
    """
    # We'll iterate over the possible slots in the workday.
    # We consider times starting from the latest overall free start time.
    candidate = work_start
    while candidate + duration <= work_end:
        slot_start = candidate
        slot_end = candidate + duration
        valid = True
        for free in free_times_lists:
            # Check if the meeting [slot_start, slot_end] can be fully contained in at least one free interval
            in_interval = any((slot_start >= interval[0] and slot_end <= interval[1]) for interval in free)
            if not in_interval:
                valid = False
                break
        if valid:
            return slot_start, slot_end
        candidate += 1  # increment candidate minute by minute
    return None

# List of free times for all participants
all_free_times = [kimberly_free, megan_free, marie_free, diana_free]

common_slot = find_common_slot(all_free_times, meeting_duration)

if common_slot:
    start_time = minutes_to_time(common_slot[0])
    end_time = minutes_to_time(common_slot[1])
    day = "Monday"
    # Output in the format HH:MM:HH:MM and the day
    print(f"{day} {start_time}:{end_time}")
else:
    print("No suitable meeting time found.")