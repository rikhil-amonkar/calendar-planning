def find_meeting_time():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30        # minutes

    # Nicole's busy times in minutes since midnight
    nicole_busy = [(9 * 60, 10 * 60), (10 * 60 + 30, 16 * 60 + 30)]
    # Judy is free all day, so only Nicole's schedule matters

    # Generate free slots for Nicole within work hours
    free_slots = []
    last_end = work_start

    for start_busy, end_busy in sorted(nicole_busy):
        if last_end < start_busy:
            free_slots.append((last_end, start_busy))
        last_end = max(last_end, end_busy)
    if last_end < work_end:
        free_slots.append((last_end, work_end))

    # Filter slots that are at least duration long
    possible_slots = [(s, e) for s, e in free_slots if e - s >= duration]

    # Apply preference: not before 16:00 (16*60 minutes)
    preferred_slots = [(s, e) for s, e in possible_slots if s >= 16 * 60]

    # Pick the first preferred slot
    if preferred_slots:
        start, end = preferred_slots[0]
        # We can start at start, end at start + duration
        meeting_start = start
        meeting_end = start + duration
    else:
        # Fallback to any possible slot
        if possible_slots:
            start, end = possible_slots[0]
            meeting_start = start
            meeting_end = start + duration
        else:
            return None, None

    # Convert back to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    return to_time(meeting_start), to_time(meeting_end)

if __name__ == "__main__":
    start_time, end_time = find_meeting_time()
    if start_time and end_time:
        print(f"Monday, {start_time}:{end_time}")
    else:
        print("No suitable time found.")