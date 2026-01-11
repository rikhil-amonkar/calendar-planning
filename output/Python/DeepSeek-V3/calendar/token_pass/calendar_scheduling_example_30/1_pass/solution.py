def time_to_minutes(t):
    """Convert HH:MM to minutes from 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes from 9:00 back to HH:MM."""
    h = 9 + m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    work_start = time_to_minutes("9:00")   # 0
    work_end = time_to_minutes("17:00")    # 480
    duration = 30

    # Busy intervals in minutes from 9:00
    jeffrey = [(30, 60), (90, 120)]
    virginia = [(0, 30), (60, 90), (330, 360), (420, 450)]
    melissa = [(0, 150), (180, 210), (240, 360), (420, 480)]

    # Combine all busy intervals
    all_busy = sorted(jeffrey + virginia + melissa)

    # Merge overlapping intervals
    merged = []
    for start, end in all_busy:
        if merged and start <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], end))
        else:
            merged.append((start, end))

    # Find free slots
    free_slots = []
    prev_end = work_start
    for start, end in merged:
        if start > prev_end and start - prev_end >= duration:
            free_slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if work_end > prev_end and work_end - prev_end >= duration:
        free_slots.append((prev_end, work_end))

    # Melissa prefers before 14:00 (300 minutes from 9:00)
    preference_limit = time_to_minutes("14:00")  # 300

    chosen_slot = None
    for start, end in free_slots:
        if start + duration <= end:
            # Check if all are free in this slot
            # Since we derived free slots from merged busy times, they are free for all.
            if start + duration <= preference_limit:
                chosen_slot = (start, start + duration)
                break
    if not chosen_slot and free_slots:
        chosen_slot = (free_slots[0][0], free_slots[0][0] + duration)

    # Output
    day = "Monday"
    start_str = minutes_to_time(chosen_slot[0])
    end_str = minutes_to_time(chosen_slot[1])
    print(f"{day}:{start_str}:{end_str}")

if __name__ == "__main__":
    main()