def parse_schedule(schedule_str):
    """Parses a string of blocked times into a list of tuples (start, end)."""
    blocked_times = []
    times = schedule_str.split(', ')
    for time in times:
        start, end = map(int, time.split(':'))
        blocked_times.append((start, end))
    return blocked_times

def find_free_slot(blocked_times, meeting_duration=1, start_time=9, end_time=17):
    """Finds a free slot of the given duration between start_time and end_time."""
    current_time = start_time
    while current_time + meeting_duration <= end_time:
        # Check if current_time to current_time + meeting_duration is free
        is_free = True
        for block_start, block_end in blocked_times:
            if not (current_time + meeting_duration <= block_start or current_time >= block_end):
                is_free = False
                break
        if is_free:
            return f"{current_time:02}:{current_time + meeting_duration:02}"
        current_time += 1
    return None

# Define the schedules
julie_schedule = "9:30, 11:30, 12:30, 14:00, 17:00"
sean_schedule = "9:30, 13:30, 15:30, 16:30"
lori_schedule = "10:30, 13:00, 15:30, 17:00"

# Parse the schedules
julie_blocked = parse_schedule(julie_schedule)
sean_blocked = parse_schedule(sean_schedule)
lori_blocked = parse_schedule(lori_schedule)

# Combine all blocked times
all_blocked_times = julie_blocked + sean_blocked + lori_blocked

# Find a free slot
free_slot = find_free_slot(all_blocked_times)

# Output the result
if free_slot:
    print(f"Monday, {free_slot[:2]}:{free_slot[2:4]}:{free_slot[4:6]}:{free_slot[6:8]}")
else:
    print("No available time slot found.")