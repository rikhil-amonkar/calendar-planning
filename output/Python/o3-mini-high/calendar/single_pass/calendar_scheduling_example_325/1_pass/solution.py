def minutes_to_hhmm(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def merge_intervals(intervals):
    # Sort intervals by start time.
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    for interval in sorted_intervals:
        if merged and interval[0] <= merged[-1][1]:
            merged[-1] = (merged[-1][0], max(merged[-1][1], interval[1]))
        else:
            merged.append(interval)
    return merged

def main():
    meeting_duration = 30  # in minutes

    # Define work hours on Monday: 9:00 to 17:00 in minutes from midnight.
    work_start = 9 * 60    # 540 minutes (9:00)
    work_end = 17 * 60     # 1020 minutes (17:00)

    # Jose’s constraint: meeting must not be after 15:30.
    # We'll require that the meeting finishes by 15:30 (i.e., end time <= 15:30).
    latest_meeting_end = 15 * 60 + 30   # 930 minutes

    # Busy intervals for each participant on Monday (times in minutes):

    busy_intervals = []
    # Jose
    busy_intervals.append((11 * 60, 11 * 60 + 30))      # 11:00 - 11:30
    busy_intervals.append((12 * 60 + 30, 13 * 60))        # 12:30 - 13:00

    # Keith
    busy_intervals.append((14 * 60, 14 * 60 + 30))        # 14:00 - 14:30
    busy_intervals.append((15 * 60, 15 * 60 + 30))        # 15:00 - 15:30

    # Logan
    busy_intervals.append((9 * 60, 10 * 60))              # 9:00 - 10:00
    busy_intervals.append((12 * 60, 12 * 60 + 30))        # 12:00 - 12:30
    busy_intervals.append((15 * 60, 15 * 60 + 30))        # 15:00 - 15:30

    # Megan
    busy_intervals.append((9 * 60, 10 * 60 + 30))         # 9:00 - 10:30
    busy_intervals.append((11 * 60, 12 * 60))             # 11:00 - 12:00
    busy_intervals.append((13 * 60, 13 * 60 + 30))        # 13:00 - 13:30
    busy_intervals.append((14 * 60 + 30, 16 * 60 + 30))   # 14:30 - 16:30

    # Gary
    busy_intervals.append((9 * 60, 9 * 60 + 30))          # 9:00 - 9:30
    busy_intervals.append((10 * 60, 10 * 60 + 30))        # 10:00 - 10:30
    busy_intervals.append((11 * 60 + 30, 13 * 60))        # 11:30 - 13:00
    busy_intervals.append((13 * 60 + 30, 14 * 60))        # 13:30 - 14:00
    busy_intervals.append((14 * 60 + 30, 16 * 60 + 30))   # 14:30 - 16:30

    # Bobby
    busy_intervals.append((11 * 60, 11 * 60 + 30))        # 11:00 - 11:30
    busy_intervals.append((12 * 60, 12 * 60 + 30))        # 12:00 - 12:30
    busy_intervals.append((13 * 60, 16 * 60))             # 13:00 - 16:00

    # Merge all the busy intervals to get the overall occupied periods.
    merged_busy = merge_intervals(busy_intervals)

    # Find free intervals within work hours.
    free_intervals = []
    # If work starts before the first busy interval.
    if work_start < merged_busy[0][0]:
        free_intervals.append((work_start, merged_busy[0][0]))
    # Gaps between busy intervals.
    for i in range(len(merged_busy) - 1):
        free_intervals.append((merged_busy[i][1], merged_busy[i+1][0]))
    # After the last busy interval until work end.
    if merged_busy[-1][1] < work_end:
        free_intervals.append((merged_busy[-1][1], work_end))

    # Look for the first free slot that fits the meeting and respects Jose's constraint.
    meeting_slot = None
    for free_start, free_end in free_intervals:
        if free_end - free_start >= meeting_duration:
            candidate_start = free_start
            candidate_end = candidate_start + meeting_duration
            if candidate_end <= latest_meeting_end:
                meeting_slot = (candidate_start, candidate_end)
                break

    # Output the result.
    if meeting_slot:
        time_range = f"{minutes_to_hhmm(meeting_slot[0])}:{minutes_to_hhmm(meeting_slot[1])}"
        print("Monday", time_range)
    else:
        print("No available meeting slot that meets the constraints.")

if __name__ == "__main__":
    main()