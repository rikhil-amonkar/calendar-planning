def main():
    # Define work hours: 9:00 to 17:00 (in minutes: 540 to 1020)
    work_start = 9 * 60   # 540 minutes (9:00)
    work_end = 17 * 60    # 1020 minutes (17:00)
    meeting_duration = 30  # minutes
    # Wayne's constraint: avoid before 14:00 (840 minutes)
    constraint_start = 14 * 60  # 840 minutes (14:00)

    # List all busy intervals in minutes (start, end) - exclusive end
    busy_intervals = []

    # Wayne: free entire day but avoids meetings before 14:00 -> add busy from 9:00 to 14:00
    busy_intervals.append((work_start, constraint_start))

    # Melissa
    busy_intervals.append((10 * 60, 11 * 60))      # 10:00-11:00 -> [600, 660)
    busy_intervals.append((12 * 60 + 30, 14 * 60))  # 12:30-14:00 -> [750, 840)
    busy_intervals.append((15 * 60, 15 * 60 + 30))  # 15:00-15:30 -> [900, 930)

    # Catherine: free all day -> no intervals

    # Gregory
    busy_intervals.append((12 * 60 + 30, 13 * 60))    # 12:30-13:00 -> [750, 780)
    busy_intervals.append((15 * 60 + 30, 16 * 60))    # 15:30-16:00 -> [930, 960)

    # Victoria
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 9:00-9:30 -> [540, 570)
    busy_intervals.append((10 * 60 + 30, 11 * 60 + 30)) # 10:30-11:30 -> [630, 690)
    busy_intervals.append((13 * 60, 14 * 60))           # 13:00-14:00 -> [780, 840)
    busy_intervals.append((14 * 60 + 30, 15 * 60))      # 14:30-15:00 -> [870, 900)
    busy_intervals.append((15 * 60 + 30, 16 * 60 + 30)) # 15:30-16:30 -> [930, 990)

    # Thomas
    busy_intervals.append((10 * 60, 12 * 60))         # 10:00-12:00 -> [600, 720)
    busy_intervals.append((12 * 60 + 30, 13 * 60))     # 12:30-13:00 -> [750, 780)
    busy_intervals.append((14 * 60 + 30, 16 * 60))     # 14:30-16:00 -> [870, 960)

    # Jennifer
    busy_intervals.append((9 * 60, 9 * 60 + 30))       # 9:00-9:30 -> [540, 570)
    busy_intervals.append((10 * 60, 10 * 60 + 30))     # 10:00-10:30 -> [600, 630)
    busy_intervals.append((11 * 60, 13 * 60))           # 11:00-13:00 -> [660, 780)
    busy_intervals.append((13 * 60 + 30, 14 * 60 + 30)) # 13:30-14:30 -> [810, 870)
    busy_intervals.append((15 * 60, 15 * 60 + 30))      # 15:00-15:30 -> [900, 930)
    busy_intervals.append((16 * 60, 16 * 60 + 30))      # 16:00-16:30 -> [960, 990)

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping busy intervals
    merged_busy = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for s, e in busy_intervals[1:]:
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged_busy.append((current_start, current_end))
                current_start, current_end = s, e
        merged_busy.append((current_start, current_end))
    else:
        merged_busy = []

    # Compute free intervals within work hours
    free_intervals = []
    prev_end = work_start
    for start, end in merged_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = end
    if prev_end < work_end:
        free_intervals.append((prev_end, work_end))

    # Find first free interval that can accommodate the meeting after constraint_start
    meeting_start = None
    for start, end in free_intervals:
        candidate_start = max(start, constraint_start)
        candidate_end = candidate_start + meeting_duration
        if candidate_end <= end:
            meeting_start = candidate_start
            meeting_end = candidate_end
            break

    # Convert meeting_start and meeting_end to time strings
    def minutes_to_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    if meeting_start is not None:
        start_str = minutes_to_time(meeting_start)
        end_str = minutes_to_time(meeting_end)
        day = "Monday"
        print(f"{day}:{start_str}:{end_str}")
    else:
        # According to the problem, there is a solution, so this should not happen.
        print("No suitable time found")

if __name__ == "__main__":
    main()