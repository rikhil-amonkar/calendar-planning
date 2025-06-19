def get_free_intervals(busy, day_start=540, day_end=1020):
    if not busy:
        return [(day_start, day_end)]
    busy_sorted = sorted(busy, key=lambda x: x[0])
    free = []
    current = day_start
    for interval in busy_sorted:
        start, end = interval
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < day_end:
        free.append((current, day_end))
    return free

mary_busy = {
    'Tuesday': [(600, 630), (930, 960)],
    'Wednesday': [(570, 600), (900, 930)],
    'Thursday': [(540, 600), (630, 690)]
}

alexis_busy = {
    'Monday': [(540, 600), (630, 720), (750, 990)],
    'Tuesday': [(540, 600), (630, 690), (720, 930), (960, 1020)],
    'Wednesday': [(540, 660), (690, 1020)],
    'Thursday': [(600, 720), (840, 870), (930, 960), (990, 1020)]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
duration = 30

for day in days:
    mary_free = get_free_intervals(mary_busy.get(day, []))
    alexis_free = get_free_intervals(alexis_busy.get(day, []))
    found = False
    for m_int in mary_free:
        for a_int in alexis_free:
            start_overlap = max(m_int[0], a_int[0])
            end_overlap = min(m_int[1], a_int[1])
            if end_overlap - start_overlap >= duration:
                meeting_start = start_overlap
                meeting_end = meeting_start + duration
                h1 = meeting_start // 60
                m1 = meeting_start % 60
                h2 = meeting_end // 60
                m2 = meeting_end % 60
                time_str = f"{h1:02d}:{m1:02d}:{h2:02d}:{m2:02d}"
                print(day)
                print(time_str)
                found = True
                break
        if found:
            break
    if found:
        break