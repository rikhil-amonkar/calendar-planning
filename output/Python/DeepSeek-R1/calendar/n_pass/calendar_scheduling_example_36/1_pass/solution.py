def main():
    # Convert time to minutes for easier calculations (using half-open intervals [start, end))
    work_start = 9 * 60  # 9:00
    work_end = 17 * 60   # 17:00
    duration = 60         # 1 hour in minutes

    # Denise constraint: available until 12:30 inclusive -> represented as [start, 751) to include 12:30
    denise_available_end = 12 * 60 + 30 + 1  # 751 minutes (12:31 is excluded)

    # Define busy intervals (half-open: [start, end))
    ryan_busy = [
        (9 * 60, 9 * 60 + 30),   # 9:00-9:30
        (12 * 60 + 30, 13 * 60)  # 12:30-13:00
    ]
    ruth_busy = []  # No meetings
    denise_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (12 * 60, 13 * 60),            # 12:00-13:00
        (14 * 60 + 30, 16 * 60 + 30)   # 14:30-16:30
    ]

    # Participants with their available times and busy slots
    participants = [
        {
            'name': 'Ryan',
            'available_start': work_start,
            'available_end': work_end,
            'busy': ryan_busy
        },
        {
            'name': 'Ruth',
            'available_start': work_start,
            'available_end': work_end,
            'busy': ruth_busy
        },
        {
            'name': 'Denise',
            'available_start': work_start,
            'available_end': denise_available_end,  # Until 12:30 inclusive (751 minutes)
            'busy': denise_busy
        }
    ]

    # Calculate free intervals for each participant
    free_intervals = []
    for participant in participants:
        free = [(participant['available_start'], participant['available_end'])]
        for (busy_start, busy_end) in participant['busy']:
            new_free = []
            for (start, end) in free:
                # If busy interval doesn't overlap, keep the free interval
                if busy_end <= start or busy_start >= end:
                    new_free.append((start, end))
                else:
                    # Split the free interval around the busy block
                    if start < busy_start:
                        new_free.append((start, busy_start))
                    if busy_end < end:
                        new_free.append((busy_end, end))
            free = new_free
        free_intervals.append(free)

    # Find intersection of free intervals across participants
    current_free = free_intervals[0]
    for i in range(1, len(free_intervals)):
        next_free = free_intervals[i]
        new_current = []
        for (s1, e1) in current_free:
            for (s2, e2) in next_free:
                low = max(s1, s2)
                high = min(e1, e2)
                if low < high:
                    new_current.append((low, high))
        current_free = new_current

    # Find first slot with sufficient duration
    meeting_start = None
    meeting_end = None
    for (start, end) in current_free:
        if end - start >= duration:
            meeting_start = start
            meeting_end = start + duration
            break

    # Convert minutes back to time strings (HH:MM)
    def format_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    start_str = format_time(meeting_start)
    end_str = format_time(meeting_end)

    # Output day and time range
    print("Monday")
    print(f"{start_str}:{end_str}")

if __name__ == "__main__":
    main()