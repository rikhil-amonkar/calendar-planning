def minutes(hour, minute):
    return hour * 60 + minute


def get_free_intervals(busy_intervals, start_day, end_day):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free_intervals = []
    prev_end = start_day
    for start, end in sorted_busy:
        if start > prev_end:
            free_intervals.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < end_day:
        free_intervals.append((prev_end, end_day))
    return free_intervals


def find_overlapping_intervals(intervals1, intervals2):
    overlapping = []
    for i1 in intervals1:
        for i2 in intervals2:
            s = max(i1[0], i2[0])
            e = min(i1[1], i2[1])
            if s < e:
                overlapping.append((s, e))
    overlapping.sort()
    return overlapping


def find_meeting_time():
    # Define busy times for each day and person
    mary_busy = {
        'Monday': [],
        'Tuesday': [
            (minutes(10, 0), minutes(10, 30)),
            (minutes(15, 30), minutes(16, 0))
        ],
        'Wednesday': [
            (minutes(9, 30), minutes(10, 0)),
            (minutes(15, 0), minutes(15, 30))
        ],
        'Thursday': [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(11, 30))
        ],
    }

    alexis_busy = {
        'Monday': [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(12, 0)),
            (minutes(12, 30), minutes(16, 30))
        ],
        'Tuesday': [
            (minutes(9, 0), minutes(10, 0)),
            (minutes(10, 30), minutes(11, 30)),
            (minutes(12, 0), minutes(15, 30)),
            (minutes(16, 0), minutes(17, 0))
        ],
        'Wednesday': [
            (minutes(9, 0), minutes(11, 0)),
            (minutes(11, 30), minutes(17, 0))
        ],
        'Thursday': [
            (minutes(10, 0), minutes(12, 0)),
            (minutes(14, 0), minutes(14, 30)),
            (minutes(15, 30), minutes(16, 0)),
            (minutes(16, 30), minutes(17, 0))
        ],
    }

    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    start_day = minutes(9, 0)   # 540
    end_day = minutes(17, 0)    # 1020

    for day in days:
        # Get busy times for Mary and Alexis
        m_busies = mary_busy[day]
        a_busies = alexis_busy[day]

        # Compute free intervals for Mary
        m_free = get_free_intervals(m_busies, start_day, end_day)
        # Compute free intervals for Alexis
        a_free = get_free_intervals(a_busies, start_day, end_day)

        # Find overlapping intervals between m_free and a_free
        overlapping = find_overlapping_intervals(m_free, a_free)

        # Check if any overlapping interval is >=30 minutes
        for interval in overlapping:
            start, end = interval
            if end - start >= 30:
                # Convert to time strings
                start_time = f"{start // 60:02d}:{start % 60:02d}"
                end_time = f"{end // 60:02d}:{end % 60:02d}"
                print(f"{start_time}:{end_time} {day}")
                return


# Run the function
find_meeting_time()
