def main():
    # Convert time string to minutes
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(total_minutes):
        hours = total_minutes // 60
        minutes = total_minutes % 60
        return f"{hours:02d}:{minutes:02d}"

    # Function to compute free intervals given busy intervals and work hours
    def free_intervals(busy_list, work_start, work_end):
        if not busy_list:
            return [(work_start, work_end)]
        sorted_busy = sorted(busy_list, key=lambda x: x[0])
        free = []
        current = work_start
        for start, end in sorted_busy:
            if current < start:
                free.append((current, start))
            current = end
        if current < work_end:
            free.append((current, work_end))
        return free

    # Function to intersect two sets of intervals
    def intersect_two(intervals1, intervals2):
        if not intervals1 or not intervals2:
            return []
        res = []
        i = j = 0
        while i < len(intervals1) and j < len(intervals2):
            low = max(intervals1[i][0], intervals2[j][0])
            high = min(intervals1[i][1], intervals2[j][1])
            if low < high:
                res.append((low, high))
            if intervals1[i][1] < intervals2[j][1]:
                i += 1
            else:
                j += 1
        return res

    # Work hours and meeting duration
    work_start_min = time_to_minutes("09:00")
    work_end_min = time_to_minutes("17:00")
    duration = 30
    avoid_after_min = time_to_minutes("15:00")  # Bobby's preference

    # Busy intervals in minutes for each participant
    lisa_busy = [
        ("09:00", "10:00"),
        ("10:30", "11:30"),
        ("12:30", "13:00"),
        ("16:00", "16:30")
    ]
    bobby_busy = [
        ("09:00", "09:30"),
        ("10:00", "10:30"),
        ("11:30", "12:00"),
        ("15:00", "15:30")
    ]
    randy_busy = [
        ("09:30", "10:00"),
        ("10:30", "11:00"),
        ("11:30", "12:30"),
        ("13:00", "13:30"),
        ("14:30", "15:30"),
        ("16:00", "16:30")
    ]

    # Convert busy times to minutes
    def convert_busy(busy_times):
        return [(time_to_minutes(s), time_to_minutes(e)) for s, e in busy_times]

    lisa_busy_min = convert_busy(lisa_busy)
    bobby_busy_min = convert_busy(bobby_busy)
    randy_busy_min = convert_busy(randy_busy)

    # Compute free intervals for each
    lisa_free = free_intervals(lisa_busy_min, work_start_min, work_end_min)
    bobby_free = free_intervals(bobby_busy_min, work_start_min, work_end_min)
    randy_free = free_intervals(randy_busy_min, work_start_min, work_end_min)

    # Find common free intervals
    common_free = intersect_two(lisa_free, bobby_free)
    common_free = intersect_two(common_free, randy_free)

    # Find the earliest 30-minute slot that ends by 15:00
    meeting_slot = None
    for start, end in common_free:
        if end - start >= duration:
            meeting_end = start + duration
            # Check if the meeting ends by 15:00 (Bobby's preference)
            if meeting_end <= avoid_after_min:
                meeting_slot = (start, meeting_end)
                break

    # If no preferred slot found, find any 30-minute slot
    if meeting_slot is None:
        for start, end in common_free:
            if end - start >= duration:
                meeting_slot = (start, start + duration)
                break

    # Format the result
    day = "Monday"
    start_time = minutes_to_time(meeting_slot[0])
    end_time = minutes_to_time(meeting_slot[1])
    time_range = f"{start_time}:{end_time}"

    print(day)
    print(time_range)

if __name__ == "__main__":
    main()