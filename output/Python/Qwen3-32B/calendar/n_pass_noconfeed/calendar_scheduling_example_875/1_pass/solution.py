def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def get_free_intervals(busy_times):
    start_work = 9 * 60  # 540
    end_work = 17 * 60   # 1020
    if not busy_times:
        return [(start_work, end_work)]
    # Convert to minutes and sort
    busy_in_min = []
    for start, end in busy_times:
        s = time_to_minutes(start)
        e = time_to_minutes(end)
        busy_in_min.append((s, e))
    # Sort by start time
    busy_in_min.sort()
    # Merge overlapping intervals
    merged = []
    for interval in busy_in_min:
        if not merged:
            merged.append(interval)
        else:
            last = merged[-1]
            if interval[0] <= last[1]:
                # Overlapping or adjacent, merge
                new_start = last[0]
                new_end = max(last[1], interval[1])
                merged[-1] = (new_start, new_end)
            else:
                merged.append(interval)
    # Generate free intervals
    free = []
    prev_end = start_work
    for s, e in merged:
        if s > prev_end:
            free.append((prev_end, s))
        prev_end = e
    # Check if there's free time after last busy
    if prev_end < end_work:
        free.append((prev_end, end_work))
    return free

natalie_schedule = {
    'Monday': [('9:00', '9:30'), ('10:00', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:30')],
    'Tuesday': [('9:00', '9:30'), ('10:00', '10:30'), ('12:30', '14:00'), ('16:00', '17:00')],
    'Wednesday': [('11:00', '11:30'), ('16:00', '16:30')],
    'Thursday': [('10:00', '11:00'), ('11:30', '15:00'), ('15:30', '16:00'), ('16:30', '17:00')],
}

william_schedule = {
    'Monday': [('9:30', '11:00'), ('11:30', '17:00')],
    'Tuesday': [('9:00', '13:00'), ('13:30', '16:00')],
    'Wednesday': [('9:00', '12:30'), ('13:00', '14:30'), ('15:30', '16:00'), ('16:30', '17:00')],
    'Thursday': [('9:00', '10:30'), ('11:00', '11:30'), ('12:00', '12:30'), ('13:00', '14:00'), ('15:00', '17:00')],
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

for day in days:
    natalie_buses = natalie_schedule[day]
    william_buses = william_schedule[day]
    natalie_free = get_free_intervals(natalie_buses)
    william_free = get_free_intervals(william_buses)
    for n_free in natalie_free:
        for w_free in william_free:
            os = max(n_free[0], w_free[0])
            oe = min(n_free[1], w_free[1])
            if os < oe and (oe - os) >= 60:
                start_time = minutes_to_time(os)
                end_time = minutes_to_time(oe)
                print(f"{day} {start_time}:{end_time}")
                exit()