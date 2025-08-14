def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def find_free_slots(blocked_intervals, work_start, work_end):
    available = [(work_start, work_end)]
    for b_start, b_end in sorted(blocked_intervals, key=lambda x: x[0]):
        new_available = []
        for interval in available:
            i_start, i_end = interval
            if i_end <= b_start or i_start >= b_end:
                new_available.append((i_start, i_end))
            else:
                if i_start < b_start:
                    new_available.append((i_start, b_start))
                if i_end > b_end:
                    new_available.append((b_end, i_end))
        available = new_available
    return available

def main():
    Monday_blocked = [
        (540, 600),  # 9:00-10:00
        (630, 1020)  # 10:30-17:00
    ]
    Tuesday_blocked = [
        (540, 570),   # 9:00-9:30
        (630, 690),   # 10:30-11:30
        (750, 810),   # 12:30-13:30
        (870, 930),   # 14:30-15:30
        (960, 1020)   # 16:00-17:00
    ]
    work_start = 540  # 9:00 AM
    work_end = 1020   # 5:00 PM (17:00)
    valid_slots = []

    # Process Monday
    blocked = Monday_blocked
    free_intervals = find_free_slots(blocked, work_start, work_end)
    for start, end in free_intervals:
        duration = end - start
        if duration >= 30:  # 30 minutes
            valid_slots.append(('Monday', start, end))

    # Process Tuesday
    blocked = Tuesday_blocked
    free_intervals = find_free_slots(blocked, work_start, work_end)
    for start, end in free_intervals:
        duration = end - start
        if duration >= 30:
            valid_slots.append(('Tuesday', start, end))

    # Sort valid slots by priority and time
    def get_priority(day, start):
        if day == 'Tuesday':
            if start >= 870:  # 14:30
                return 0
            else:
                return 1
        else:
            return 2

    valid_slots.sort(key=lambda x: (get_priority(x[0], x[1]), x[1]))

    # Output the best slot
    best_slot = valid_slots[0]
    day = best_slot[0]
    start_time = best_slot[1]
    end_time = best_slot[2]

    start_str = minutes_to_time(start_time)
    end_str = minutes_to_time(end_time)

    print(f"{day} {start_str}:{end_str}")

if __name__ == "__main__":
    main()