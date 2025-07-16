def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from 9:00)
    work_start = 0       # 9:00 is 0 minutes
    work_end = 480       # 17:00 is 480 minutes (8 hours * 60)
    meeting_duration = 30  # 30 minutes

    # Busy intervals for each participant (in minutes from 9:00)
    # Eric: no meetings -> empty
    # Ashley: [10:00-10:30], [11:00-12:00], [12:30-13:00], [15:00-16:00]
    ashley = [[60, 90], [120, 180], [210, 240], [360, 420]]
    # Ronald: [9:00-9:30], [10:00-11:30], [12:30-14:00], [14:30-17:00]
    ronald = [[0, 30], [60, 150], [210, 300], [330, 480]]
    # Larry: [9:00-12:00], [13:00-17:00]
    larry = [[0, 180], [240, 480]]
    # Eric: no meetings

    # Combine all busy intervals
    busy_intervals = ashley + ronald + larry
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping intervals
    merged = []
    for interval in busy_intervals:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                merged[-1][1] = max(last[1], interval[1])
            else:
                merged.append(interval)

    # Calculate free intervals within work hours
    free_intervals = []
    # Before first meeting
    if merged[0][0] > work_start:
        free_intervals.append([work_start, merged[0][0]])
    # Between meetings
    for i in range(len(merged) - 1):
        free_start = merged[i][1]
        free_end = merged[i+1][0]
        if free_start < free_end:
            free_intervals.append([free_start, free_end])
    # After last meeting
    if merged[-1][1] < work_end:
        free_intervals.append([merged[-1][1], work_end])

    # Find the first free interval that fits the meeting duration
    meeting_start = None
    for interval in free_intervals:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_start = start
            meeting_end = start + meeting_duration
            break

    # Convert meeting start and end to time strings
    def minutes_to_time(total_minutes):
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    start_time_str = minutes_to_time(meeting_start)
    end_time_str = minutes_to_time(meeting_end)
    time_range = f"{start_time_str}:{end_time_str}"

    # Output results
    print("Monday")
    print(time_range)

if __name__ == "__main__":
    main()