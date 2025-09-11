def main():
    # Work hours: 9:00 to 17:00 (540 to 1020 minutes)
    work_start = 540
    work_end = 1020
    meeting_duration = 30

    # Wednesday busy intervals in minutes
    nancy_busy = [[600, 690], [810, 960]]
    jose_busy = [[540, 570], [600, 750], [810, 870], [900, 1020]]

    # Compute free intervals for Nancy
    nancy_free = []
    current = work_start
    for start, end in sorted(nancy_busy):
        if current < start:
            nancy_free.append([current, start])
        current = end
    if current < work_end:
        nancy_free.append([current, work_end])

    # Compute free intervals for Jose
    jose_free = []
    current = work_start
    for start, end in sorted(jose_busy):
        if current < start:
            jose_free.append([current, start])
        current = end
    if current < work_end:
        jose_free.append([current, work_end])

    # Find overlapping free intervals
    candidates = []
    for n_start, n_end in nancy_free:
        for j_start, j_end in jose_free:
            start = max(n_start, j_start)
            end = min(n_end, j_end)
            if end - start >= meeting_duration:
                candidates.append((start, end))

    # Select the earliest candidate
    candidates.sort()
    start_min, end_min = candidates[0]

    # Convert minutes to HH:MM format
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    start_str = format_time(start_min)
    end_str = format_time(end_min)
    print(f"Wednesday {start_str}:{end_str}")

if __name__ == "__main__":
    main()