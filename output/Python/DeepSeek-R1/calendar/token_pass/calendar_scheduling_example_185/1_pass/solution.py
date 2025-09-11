def main():
    # Define work hours in minutes from 9:00 (0) to 17:00 (480)
    work_start = 0
    work_end = 480
    meeting_duration = 30

    # Busy intervals for each participant in minutes (exclusive end)
    busy_intervals = [
        [0, 60],    # Megan: avoid before 10:00
        [30, 60],   # Diana: 9:30-10:00
        [60, 90],   # Kimberly: 10:00-10:30
        [60, 120],  # Marie: 10:00-11:00
        [90, 330],  # Diana: 10:30-14:30
        [120, 180], # Kimberly: 11:00-12:00
        [150, 360], # Marie: 11:30-15:00
        [390, 480], # Diana: 15:30-17:00
        [420, 450], # Kimberly: 16:00-16:30
        [420, 450]  # Marie: 16:00-16:30
    ]

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping busy intervals
    merged_busy = []
    current_start, current_end = busy_intervals[0]
    for interval in busy_intervals[1:]:
        if interval[0] <= current_end:
            current_end = max(current_end, interval[1])
        else:
            merged_busy.append([current_start, current_end])
            current_start, current_end = interval
    merged_busy.append([current_start, current_end])

    # Find free intervals within work hours
    free_intervals = []
    prev_end = work_start
    for busy in merged_busy:
        if busy[0] > prev_end:
            free_intervals.append([prev_end, busy[0]])
        prev_end = max(prev_end, busy[1])
    if prev_end < work_end:
        free_intervals.append([prev_end, work_end])

    # Find the first free interval that can accommodate the meeting
    meeting_slot = None
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_slot = (start, start + meeting_duration)
            break

    # Convert minutes back to time strings
    def minutes_to_time(minutes):
        total_minutes = 9 * 60 + minutes
        h = total_minutes // 60
        m = total_minutes % 60
        return f"{h:02d}:{m:02d}"

    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])

    # Output the day and time range
    print("Monday")
    print(f"{start_time}:{end_time}")

if __name__ == "__main__":
    main()