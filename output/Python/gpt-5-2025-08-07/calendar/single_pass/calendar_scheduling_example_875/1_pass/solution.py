from datetime import timedelta

def to_minutes(t):
    h, m = map(int, t.split(":"))
    return h * 60 + m

def to_hhmm(m):
    h = m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def merge_intervals(intervals):
    if not intervals:
        return []
    intervals = sorted(intervals)
    merged = [intervals[0]]
    for s, e in intervals[1:]:
        last_s, last_e = merged[-1]
        if s <= last_e:
            merged[-1] = (last_s, max(last_e, e))
        else:
            merged.append((s, e))
    return merged

def subtract_intervals(base_interval, busy_intervals):
    # base_interval: (start, end)
    # busy_intervals: list of (start, end)
    start, end = base_interval
    free = [(start, end)]
    for b_start, b_end in merge_intervals([i for i in busy_intervals if i[1] > start and i[0] < end]):
        new_free = []
        for f_start, f_end in free:
            if b_end <= f_start or b_start >= f_end:
                new_free.append((f_start, f_end))
            else:
                if f_start < b_start:
                    new_free.append((f_start, b_start))
                if b_end < f_end:
                    new_free.append((b_end, f_end))
        free = new_free
        if not free:
            break
    return free

def intersect_intervals(a_list, b_list):
    i = j = 0
    result = []
    while i < len(a_list) and j < len(b_list):
        a_start, a_end = a_list[i]
        b_start, b_end = b_list[j]
        start = max(a_start, b_start)
        end = min(a_end, b_end)
        if start < end:
            result.append((start, end))
        if a_end < b_end:
            i += 1
        else:
            j += 1
    return result

# Schedules
days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

work_start = to_minutes("09:00")
work_end = to_minutes("17:00")
work_interval = (work_start, work_end)

meeting_duration = 60  # minutes

natalie = {
    "Monday":    [("09:00","09:30"),("10:00","12:00"),("12:30","13:00"),("14:00","14:30"),("15:00","16:30")],
    "Tuesday":   [("09:00","09:30"),("10:00","10:30"),("12:30","14:00"),("16:00","17:00")],
    "Wednesday": [("11:00","11:30"),("16:00","16:30")],
    "Thursday":  [("10:00","11:00"),("11:30","15:00"),("15:30","16:00"),("16:30","17:00")],
}

william = {
    "Monday":    [("09:30","11:00"),("11:30","17:00")],
    "Tuesday":   [("09:00","13:00"),("13:30","16:00")],
    "Wednesday": [("09:00","12:30"),("13:00","14:30"),("15:30","16:00"),("16:30","17:00")],
    "Thursday":  [("09:00","10:30"),("11:00","11:30"),("12:00","12:30"),("13:00","14:00"),("15:00","17:00")],
}

def convert_schedule_to_minutes(sched):
    out = {}
    for d, intervals in sched.items():
        out[d] = [(to_minutes(s), to_minutes(e)) for s, e in intervals]
    return out

natalie_m = convert_schedule_to_minutes(natalie)
william_m = convert_schedule_to_minutes(william)

def find_meeting():
    for day in days:
        # Compute free intervals within work hours
        nat_free = subtract_intervals(work_interval, natalie_m.get(day, []))
        wil_free = subtract_intervals(work_interval, william_m.get(day, []))
        # Intersect frees
        overlap = intersect_intervals(nat_free, wil_free)
        # Find a block with enough duration
        for s, e in overlap:
            if e - s >= meeting_duration:
                start_time = s
                end_time = s + meeting_duration
                return day, start_time, end_time
    return None

result = find_meeting()
if result:
    day, start_m, end_m = result
    time_range = f"{to_hhmm(start_m)}:{to_hhmm(end_m)}"
    print(day)
    print(f"{{{time_range}}}")
else:
    print("No available time found")