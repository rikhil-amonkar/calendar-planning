def time_to_minutes(t):
    h, m = t.split(":")
    return int(h) * 60 + int(m)


def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"


def invert_intervals(busy_intervals, work_start, work_end):
    busy_intervals_sorted = sorted(busy_intervals, key=lambda x: time_to_minutes(x[0]))
    free = []
    current_start = work_start
    for interval in busy_intervals_sorted:
        bstart = time_to_minutes(interval[0])
        bend = time_to_minutes(interval[1])
        if current_start < bstart:
            free.append((current_start, bstart))
        current_start = max(current_start, bend)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free


def intersect_intervals(intervals1, intervals2):
    i, j = 0, 0
    result = []
    while i < len(intervals1) and j < len(intervals2):
        start = max(intervals1[i][0], intervals2[j][0])
        end = min(intervals1[i][1], intervals2[j][1])
        if start < end:
            result.append((start, end))
        if intervals1[i][1] < intervals2[j][1]:
            i += 1
        else:
            j += 1
    return result


def main():
    # Meeting constraints: 30 minutes on Monday between 09:00 and 17:00
    meeting_day = "Monday"
    meeting_duration = 30  # in minutes
    work_start = time_to_minutes("09:00")
    work_end = time_to_minutes("17:00")

    # Busy intervals for each participant on Monday
    eric_busy = []  # Eric has no meetings
    ashley_busy = [("10:00", "10:30"), ("11:00", "12:00"),
                   ("12:30", "13:00"), ("15:00", "16:00")]
    ronald_busy = [("09:00", "09:30"), ("10:00", "11:30"),
                   ("12:30", "14:00"), ("14:30", "17:00")]
    larry_busy = [("09:00", "12:00"), ("13:00", "17:00")]

    # Calculate free intervals for each participant
    eric_free = [(work_start, work_end)]  # available all day
    ashley_free = invert_intervals(ashley_busy, work_start, work_end)
    ronald_free = invert_intervals(ronald_busy, work_start, work_end)
    larry_free = invert_intervals(larry_busy, work_start, work_end)

    # Find common free slots by intersecting free intervals
    common_free = intersect_intervals(eric_free, ashley_free)
    common_free = intersect_intervals(common_free, ronald_free)
    common_free = intersect_intervals(common_free, larry_free)

    # Choose the first interval that fits the meeting duration
    meeting_slot = None
    for slot in common_free:
        if slot[1] - slot[0] >= meeting_duration:
            meeting_slot = (slot[0], slot[0] + meeting_duration)
            break

    if meeting_slot:
        start_time = minutes_to_time(meeting_slot[0])
        end_time = minutes_to_time(meeting_slot[1])
        print(f"{meeting_day} {start_time}:{end_time}")
    else:
        print("No available meeting slot")


if __name__ == "__main__":
    main()