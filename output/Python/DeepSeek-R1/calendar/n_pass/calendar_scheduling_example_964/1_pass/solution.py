def main():
    work_start = 540   # 9:00 in minutes from midnight
    work_end = 1020    # 17:00

    def minute_to_time(minute):
        hours = minute // 60
        minutes = minute % 60
        return f"{hours:02d}:{minutes:02d}"

    # Busy intervals for Tuesday for Betty and Megan (in minutes from midnight)
    betty_busy = [
        (570, 600),   # 9:30-10:00
        (630, 660),   # 10:30-11:00
        (720, 750),   # 12:00-12:30
        (810, 900),   # 13:30-15:00
        (990, 1020)   # 16:30-17:00
    ]

    megan_busy = [
        (540, 570),   # 9:00-9:30
        (600, 630),   # 10:00-10:30
        (720, 840),   # 12:00-14:00
        (900, 930),   # 15:00-15:30
        (960, 990)    # 16:00-16:30
    ]

    def get_free_intervals(busy_list, start, end):
        if not busy_list:
            return [(start, end)]
        busy_list.sort(key=lambda x: x[0])
        free = []
        current = start
        for s, e in busy_list:
            if current < s:
                free.append((current, s))
            current = max(current, e)
        if current < end:
            free.append((current, end))
        return free

    betty_free = get_free_intervals(betty_busy, work_start, work_end)
    megan_free = get_free_intervals(megan_busy, work_start, work_end)

    found_interval = None
    for b_start, b_end in betty_free:
        for m_start, m_end in megan_free:
            start_overlap = max(b_start, m_start)
            end_overlap = min(b_end, m_end)
            if end_overlap - start_overlap >= 60:
                found_interval = (start_overlap, end_overlap)
                break
        if found_interval:
            break

    day = "Tuesday"
    start_time_str = minute_to_time(found_interval[0])
    end_time_str = minute_to_time(found_interval[1])
    time_range_str = f"{start_time_str}:{end_time_str}"

    print(day)
    print(time_range_str)

if __name__ == "__main__":
    main()