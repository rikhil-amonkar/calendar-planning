def main():
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60   # 17:00 in minutes
    duration = 30         # meeting duration in minutes

    # Define busy times in minutes for each day (start, end)
    arthur_busy = {
        'Monday': [
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (13 * 60 + 30, 14 * 60),    # 13:30-14:00
            (15 * 60, 15 * 60 + 30)     # 15:00-15:30
        ],
        'Wednesday': [
            (10 * 60, 10 * 60 + 30),    # 10:00-10:30
            (11 * 60, 11 * 60 + 30),    # 11:00-11:30
            (12 * 60, 12 * 60 + 30),    # 12:00-12:30
            (14 * 60, 14 * 60 + 30),    # 14:00-14:30
            (16 * 60, 16 * 60 + 30)     # 16:00-16:30
        ]
    }

    michael_busy = {
        'Monday': [
            (9 * 60, 12 * 60),          # 9:00-12:00
            (12 * 60 + 30, 13 * 60),    # 12:30-13:00
            (14 * 60, 14 * 60 + 30),    # 14:00-14:30
            (15 * 60, 17 * 60)          # 15:00-17:00
        ],
        'Wednesday': [
            (10 * 60, 12 * 60 + 30),    # 10:00-12:30
            (13 * 60, 13 * 60 + 30)     # 13:00-13:30
        ]
    }

    days = ['Monday', 'Wednesday']  # Skip Tuesday as Arthur cannot meet

    found_slot = None
    for day in days:
        # Get busy intervals for the day and sort by start time
        a_busy = sorted(arthur_busy.get(day, []))
        m_busy = sorted(michael_busy.get(day, []))

        # Compute free intervals for Arthur
        a_free = []
        current = work_start
        for s, e in a_busy:
            if current < s:
                a_free.append((current, s))
            current = e
        if current < work_end:
            a_free.append((current, work_end))

        # Compute free intervals for Michael
        m_free = []
        current = work_start
        for s, e in m_busy:
            if current < s:
                m_free.append((current, s))
            current = e
        if current < work_end:
            m_free.append((current, work_end))

        # Find overlapping free intervals
        i = j = 0
        while i < len(a_free) and j < len(m_free):
            a_start, a_end = a_free[i]
            m_start, m_end = m_free[j]
            # Calculate overlap
            low = max(a_start, m_start)
            high = min(a_end, m_end)
            if low < high and high - low >= duration:
                found_slot = (day, low, low + duration)
                break
            # Move to next interval
            if a_end < m_end:
                i += 1
            else:
                j += 1
        if found_slot:
            break

    if found_slot:
        day, start_min, end_min = found_slot
        # Format time as HH:MM:HH:MM
        start_hour = start_min // 60
        start_minute = start_min % 60
        end_hour = end_min // 60
        end_minute = end_min % 60
        time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
        print(day)
        print(time_str)
    else:
        print("No solution found")  # Should not happen per problem

if __name__ == "__main__":
    main()