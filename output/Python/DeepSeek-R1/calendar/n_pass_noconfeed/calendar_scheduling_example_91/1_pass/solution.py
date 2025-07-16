def main():
    # Work hours: 9:00 to 17:00 (converted to minutes from 9:00)
    work_start = 0      # 9:00
    work_end = 480      # 17:00 (8 hours * 60 minutes)
    meeting_duration = 60  # 60 minutes

    # Collect all busy intervals in minutes (relative to 9:00)
    busy_intervals = []

    # Danielle's meetings
    busy_intervals.append((0, 60))     # 9:00-10:00
    busy_intervals.append((90, 120))    # 10:30-11:00
    busy_intervals.append((330, 360))   # 14:30-15:00
    busy_intervals.append((390, 420))   # 15:30-16:00
    busy_intervals.append((450, 480))   # 16:30-17:00

    # Bruce's meetings
    busy_intervals.append((120, 150))   # 11:00-11:30
    busy_intervals.append((210, 240))   # 12:30-13:00
    busy_intervals.append((300, 330))   # 14:00-14:30
    busy_intervals.append((390, 420))   # 15:30-16:00

    # Eric's meetings
    busy_intervals.append((0, 30))      # 9:00-9:30
    busy_intervals.append((60, 120))    # 10:00-11:00
    busy_intervals.append((150, 240))   # 11:30-13:00
    busy_intervals.append((330, 390))   # 14:30-15:30

    # Sort busy intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping or adjacent intervals
    merged_busy = []
    if busy_intervals:
        merged_busy = [busy_intervals[0]]
        for i in range(1, len(busy_intervals)):
            current_start, current_end = busy_intervals[i]
            last_start, last_end = merged_busy[-1]
            if current_start <= last_end:
                merged_busy[-1] = (last_start, max(last_end, current_end))
            else:
                merged_busy.append((current_start, current_end))

    # Find free intervals within work hours
    free_intervals = []
    current = work_start
    for start_busy, end_busy in merged_busy:
        if current < start_busy:
            free_intervals.append((current, start_busy))
        current = end_busy
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find the first free interval that can fit the meeting
    meeting_start = None
    for start_free, end_free in free_intervals:
        if end_free - start_free >= meeting_duration:
            meeting_start = start_free
            break

    # Convert meeting start and end from minutes to time strings
    def minutes_to_time(total_minutes):
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    meeting_end = meeting_start + meeting_duration
    start_str = minutes_to_time(meeting_start)
    end_str = minutes_to_time(meeting_end)

    # Output day and time range in HH:MM:HH:MM format
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()