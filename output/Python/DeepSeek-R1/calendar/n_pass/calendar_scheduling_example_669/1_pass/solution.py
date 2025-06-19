def main():
    work_start = 9 * 60  # 9:00 in minutes from midnight
    work_end = 17 * 60   # 17:00

    # Define busy intervals for each participant per day (in minutes from midnight)
    jean_busy_monday = []
    jean_busy_tuesday = [
        (11*60 + 30, 12*60),   # 11:30 to 12:00
        (16*60, 16*60 + 30)     # 16:00 to 16:30
    ]
    doris_busy_monday = [
        (9*60, 11*60 + 30),     # 9:00 to 11:30
        (12*60, 12*60 + 30),    # 12:00 to 12:30
        (13*60 + 30, 16*60),    # 13:30 to 16:00
        (16*60 + 30, 17*60)     # 16:30 to 17:00
    ]
    doris_busy_tuesday = [
        (9*60, 17*60)            # 9:00 to 17:00
    ]

    candidate = None
    candidate_day = None

    for day in ['Monday', 'Tuesday']:
        if day == 'Monday':
            busy = jean_busy_monday + doris_busy_monday
        else:
            busy = jean_busy_tuesday + doris_busy_tuesday

        # Sort busy intervals by start time
        sorted_busy = sorted(busy, key=lambda x: x[0])
        merged_busy = []
        if sorted_busy:
            current_start, current_end = sorted_busy[0]
            for i in range(1, len(sorted_busy)):
                s, e = sorted_busy[i]
                if s <= current_end:
                    current_end = max(current_end, e)
                else:
                    merged_busy.append((current_start, current_end))
                    current_start, current_end = s, e
            merged_busy.append((current_start, current_end))

        # Compute free intervals within work hours
        free = []
        current = work_start
        for interval in merged_busy:
            s, e = interval
            if current < s:
                free.append((current, s))
            current = e
        if current < work_end:
            free.append((current, work_end))

        # Find a candidate meeting time
        if day == 'Monday':
            # First, try to find a slot entirely before 14:00 (840 minutes)
            for interval in free:
                s, e = interval
                if e - s >= 30:  # Check if the interval is long enough
                    if s + 30 <= 14 * 60:  # Ensure meeting ends by 14:00
                        candidate = (s, s + 30)
                        candidate_day = day
                        break
            if candidate is None:
                # If no slot before 14:00, take any available slot on Monday
                for interval in free:
                    s, e = interval
                    if e - s >= 30:
                        candidate = (s, s + 30)
                        candidate_day = day
                        break
        else:  # Tuesday
            for interval in free:
                s, e = interval
                if e - s >= 30:
                    candidate = (s, s + 30)
                    candidate_day = day
                    break

        if candidate is not None:
            break

    if candidate is None:
        print("No solution found")
        exit(1)

    # Convert candidate times to HH:MM format
    s, e = candidate
    start_hour = s // 60
    start_minute = s % 60
    end_hour = e // 60
    end_minute = e % 60
    time_str = f"{start_hour}:{start_minute:02d}:{end_hour}:{end_minute:02d}"

    print(candidate_day)
    print(time_str)

if __name__ == "__main__":
    main()