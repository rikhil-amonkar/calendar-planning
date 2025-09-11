def get_free_intervals(work_start, work_end, busy_intervals):
    # Sort busy intervals by start time
    busy = sorted(busy_intervals)
    free = []
    current_start = work_start
    for start, end in busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def find_meeting_time():
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
    work_start = 9 * 60  # 540 minutes
    work_end = 17 * 60   # 1020 minutes
    carl_busy = {
        'Monday': [(660, 690)],  # 11:00-11:30
        'Tuesday': [(870, 900)],  # 14:30-15:00
        'Wednesday': [(600, 690), (780, 810)],  # 10:00-11:30, 13:00-13:30
        'Thursday': [(810, 840), (960, 990)],  # 13:30-14:00, 16:00-16:30
    }
    margaret_busy = {
        'Monday': [(540, 630), (660, 1020)],  # 9:00-10:30, 11:00-17:00
        'Tuesday': [(570, 720), (810, 840), (930, 1020)],  # 9:30-12:00, 13:30-14:00, 15:30-17:00
        'Wednesday': [(570, 720), (750, 780), (810, 870), (900, 1020)],  # 9:30-12:00, 12:30-13:00, 13:30-14:30, 15:00-17:00
        'Thursday': [(600, 720), (750, 840), (870, 1020)],  # 10:00-12:00, 12:30-14:00, 14:30-17:00
    }

    valid_slots = []

    for day in days:
        # Compute Carl's and Margaret's free intervals
        c_free = get_free_intervals(work_start, work_end, carl_busy.get(day, []))
        m_free = get_free_intervals(work_start, work_end, margaret_busy.get(day, []))

        # Find overlapping intervals
        for c_start, c_end in c_free:
            for m_start, m_end in m_free:
                start = max(c_start, m_start)
                end = min(c_end, m_end)
                if start < end and (end - start) >= 60:
                    valid_slots.append((day, start, end))

    # Sort valid slots by day priority and start time
    def sort_key(slot):
        day_priority = {'Monday': 0, 'Tuesday': 1, 'Wednesday': 2, 'Thursday': 3}
        day, start, end = slot
        return (day_priority[day], start)

    if valid_slots:
        sorted_slots = sorted(valid_slots, key=sort_key)
        best_day, best_start, best_end = sorted_slots[0]
        start_time = f"{best_start // 60:02d}:{best_start % 60:02d}"
        end_time = f"{best_end // 60:02d}:{best_end % 60:02d}"
        print(f"{start_time}:{end_time} {best_day}")
    else:
        print("No suitable time found")

find_meeting_time()