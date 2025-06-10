def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes (from 9:00)
    work_start = 0
    work_end = 480  # 17:00 - 9:00 = 8 hours * 60 minutes

    # James' busy times in minutes from 9:00
    james_busy = [
        (11*60 + 30 - 9*60, 12*60 - 9*60),    # 11:30 to 12:00 -> (150, 180)
        (14*60 + 30 - 9*60, 15*60 - 9*60)      # 14:30 to 15:00 -> (330, 360)
    ]

    # John's busy times in minutes from 9:00
    john_busy = [
        (9*60 + 30 - 9*60, 11*60 - 9*60),      # 9:30 to 11:00 -> (30, 120)
        (11*60 + 30 - 9*60, 12*60 - 9*60),     # 11:30 to 12:00 -> (150, 180)
        (12*60 + 30 - 9*60, 13*60 + 30 - 9*60), # 12:30 to 13:30 -> (210, 270)
        (14*60 + 30 - 9*60, 16*60 + 30 - 9*60)  # 14:30 to 16:30 -> (330, 450)
    ]

    # Combine all busy intervals
    busy_intervals = james_busy + john_busy

    # Sort the intervals by start time
    busy_intervals.sort(key=lambda x: x[0])

    # Merge overlapping or adjacent intervals
    merged = []
    if busy_intervals:
        current_start, current_end = busy_intervals[0]
        for i in range(1, len(busy_intervals)):
            s, e = busy_intervals[i]
            if s <= current_end:
                current_end = max(current_end, e)
            else:
                merged.append((current_start, current_end))
                current_start, current_end = s, e
        merged.append((current_start, current_end))

    # Find free intervals
    free_intervals = []
    current = work_start
    for start, end in merged:
        if current < start:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))

    # Find the first free interval that is at least 60 minutes
    meeting_start_min = None
    for start, end in free_intervals:
        if end - start >= 60:
            meeting_start_min = start
            break

    if meeting_start_min is None:
        print("No suitable meeting time found.")
        return

    # Calculate meeting end time
    meeting_end_min = meeting_start_min + 60

    # Convert meeting start time to string
    total_minutes = meeting_start_min
    hours = total_minutes // 60
    minutes = total_minutes % 60
    start_hour = 9 + hours
    start_time = f"{start_hour}:{minutes:02d}"

    # Convert meeting end time to string
    total_minutes_end = meeting_end_min
    hours_end = total_minutes_end // 60
    minutes_end = total_minutes_end % 60
    end_hour = 9 + hours_end
    end_time = f"{end_hour}:{minutes_end:02d}"

    print(f"Monday, {start_time}, {end_time}")

if __name__ == "__main__":
    main()