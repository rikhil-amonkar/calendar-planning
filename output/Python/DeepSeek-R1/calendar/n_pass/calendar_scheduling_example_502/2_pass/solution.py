def main():
    # Work hours: 9:00 to 17:00
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes

    # Constraint: meeting must end by 12:30 (750 minutes from midnight)
    constraint_end = 12 * 60 + 30  # 750 minutes

    # Jack's busy intervals in minutes (start, end)
    jack_busy = [
        (9*60+30, 10*60+30),   # 9:30-10:30
        (11*60, 11*60+30),      # 11:00-11:30
        (12*60+30, 13*60),      # 12:30-13:00
        (14*60, 14*60+30),      # 14:00-14:30
        (16*60, 16*60+30)       # 16:00-16:30
    ]

    # Charlotte's busy intervals in minutes (start, end)
    charlotte_busy = [
        (9*60+30, 10*60),       # 9:30-10:00
        (10*60+30, 12*60),      # 10:30-12:00
        (12*60+30, 13*60+30),   # 12:30-13:30
        (14*60, 16*60)          # 14:00-16:00
    ]

    # Combine busy intervals
    busy = jack_busy + charlotte_busy
    if not busy:
        merged_busy = []
    else:
        busy.sort(key=lambda x: x[0])
        merged_busy = []
        start, end = busy[0]
        for i in range(1, len(busy)):
            s, e = busy[i]
            if s <= end:
                end = max(end, e)
            else:
                merged_busy.append((start, end))
                start, end = s, e
        merged_busy.append((start, end))

    # Calculate free intervals within work hours
    free_intervals = []
    if not merged_busy:
        free_intervals.append((work_start, work_end))
    else:
        # Before first busy interval
        if work_start < merged_busy[0][0]:
            free_intervals.append((work_start, merged_busy[0][0]))
        # Between busy intervals
        for i in range(len(merged_busy)-1):
            current_end = merged_busy[i][1]
            next_start = merged_busy[i+1][0]
            if current_end < next_start:
                free_intervals.append((current_end, next_start))
        # After last busy interval
        if merged_busy[-1][1] < work_end:
            free_intervals.append((merged_busy[-1][1], work_end))

    # Find a meeting slot that ends by constraint_end
    meeting_slot = None
    for interval in free_intervals:
        s, e = interval
        effective_end = min(e, constraint_end)
        if effective_end - s >= 30:
            meeting_slot = (s, s + 30)
            break

    # Convert the meeting slot to time strings
    def format_time(minutes):
        h = minutes // 60
        m = minutes % 60
        return f"{h:02d}:{m:02d}"

    if meeting_slot:
        start_time = format_time(meeting_slot[0])
        end_time = format_time(meeting_slot[1])
        time_range_str = f"{start_time}:{end_time}"
        print(time_range_str)
        print("Monday")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()