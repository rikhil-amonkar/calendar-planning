def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes

    # Convert minutes since midnight to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours:02d}:{mins:02d}"

    # Find free intervals given busy intervals and time range
    def find_free_intervals(busy_intervals, start_min, end_min):
        free = []
        current = start_min
        for busy in sorted(busy_intervals, key=lambda x: x[0]):
            if current < busy[0]:
                free.append([current, busy[0]])
            current = max(current, busy[1])
        if current < end_min:
            free.append([current, end_min])
        return free

    # Intersect two sets of intervals
    def intersect_intervals(intervals1, intervals2):
        i = j = 0
        common = []
        while i < len(intervals1) and j < len(intervals2):
            start1, end1 = intervals1[i]
            start2, end2 = intervals2[j]
            overlap_start = max(start1, start2)
            overlap_end = min(end1, end2)
            if overlap_start < overlap_end:
                common.append([overlap_start, overlap_end])
            if end1 < end2:
                i += 1
            else:
                j += 1
        return common

    # Parameters
    day = "Monday"
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30
    helen_constraint = time_to_minutes("13:30")  # Helen doesn't want to meet after 13:30

    # Margaret's busy intervals in minutes
    margaret_busy = [
        [time_to_minutes("9:00"), time_to_minutes("10:00")],
        [time_to_minutes("10:30"), time_to_minutes("11:00")],
        [time_to_minutes("11:30"), time_to_minutes("12:00")],
        [time_to_minutes("13:00"), time_to_minutes("13:30")],
        [time_to_minutes("15:00"), time_to_minutes("15:30")]
    ]

    # Donna's busy intervals in minutes
    donna_busy = [
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("16:00"), time_to_minutes("16:30")]
    ]

    # Helen's busy intervals in minutes
    helen_busy = [
        [time_to_minutes("9:00"), time_to_minutes("9:30")],
        [time_to_minutes("10:00"), time_to_minutes("11:30")],
        [time_to_minutes("13:00"), time_to_minutes("14:00")],
        [time_to_minutes("14:30"), time_to_minutes("15:00")],
        [time_to_minutes("15:30"), time_to_minutes("17:00")]
    ]

    # Apply Helen's constraint: only consider up to 13:30
    effective_end = min(work_end, helen_constraint)

    # Find free intervals for each person within [work_start, effective_end]
    margaret_free = find_free_intervals(margaret_busy, work_start, effective_end)
    donna_free = find_free_intervals(donna_busy, work_start, effective_end)
    helen_free = find_free_intervals(helen_busy, work_start, effective_end)

    # Find common free intervals
    common_free = intersect_intervals(margaret_free, donna_free)
    common_free = intersect_intervals(common_free, helen_free)

    # Find the first common interval that can accommodate the meeting
    meeting_time = None
    for interval in common_free:
        start, end = interval
        if end - start >= meeting_duration:
            meeting_time = (start, start + meeting_duration)
            break

    # Format output
    if meeting_time:
        start_time_str = minutes_to_time(meeting_time[0])
        end_time_str = minutes_to_time(meeting_time[1])
        print(f"{day} {start_time_str}:{end_time_str}")
    else:
        print("No suitable time found")

if __name__ == "__main__":
    main()