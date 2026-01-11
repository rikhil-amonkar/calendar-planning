def time_to_min(t):
    # t is "HH:MM"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def add_busy(day_schedule, start, end):
    # start, end in "HH:MM"
    s = time_to_min(start) - 9*60  # offset from 9:00
    e = time_to_min(end) - 9*60
    if s < 0: s = 0
    if e > 480: e = 480
    if s < e:
        day_schedule.append((s, e))

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    for start, end in sorted_intervals:
        if not merged or merged[-1][1] < start:
            merged.append([start, end])
        else:
            merged[-1][1] = max(merged[-1][1], end)
    return merged

def find_free_slots(busy_intervals, day_start_min, day_end_min):
    # busy_intervals already in minutes from 9:00
    merged = merge_intervals(busy_intervals)
    free = []
    prev_end = day_start_min
    for start, end in merged:
        if start > prev_end:
            free.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < day_end_min:
        free.append((prev_end, day_end_min))
    return free

def intersect_slots(slots1, slots2, min_duration):
    result = []
    i = j = 0
    while i < len(slots1) and j < len(slots2):
        s1, e1 = slots1[i]
        s2, e2 = slots2[j]
        start = max(s1, s2)
        end = min(e1, e2)
        if start < end:
            if end - start >= min_duration:
                result.append((start, end))
        if e1 < e2:
            i += 1
        else:
            j += 1
    return result

def main():
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]
    work_start = 9 * 60
    work_end = 17 * 60
    duration = 60

    # Laura's schedule
    laura_busy = {
        "Monday": [("10:30", "11:00"), ("12:30", "13:00"), ("14:30", "15:30"), ("16:00", "17:00")],
        "Tuesday": [("9:30", "10:00"), ("11:00", "11:30"), ("13:00", "13:30"), ("14:30", "15:00"), ("16:00", "17:00")],
        "Wednesday": [("11:30", "12:00"), ("12:30", "13:00"), ("15:30", "16:30")],
        "Thursday": [("10:30", "11:00"), ("12:00", "13:30"), ("15:00", "15:30"), ("16:00", "16:30")]
    }

    # Philip's schedule
    philip_busy = {
        "Monday": [("9:00", "17:00")],
        "Tuesday": [("9:00", "11:00"), ("11:30", "12:00"), ("13:00", "13:30"), ("14:00", "14:30"), ("15:00", "16:30")],
        "Wednesday": [("9:00", "10:00"), ("11:00", "12:00"), ("12:30", "16:00"), ("16:30", "17:00")],
        "Thursday": [("9:00", "10:30"), ("11:00", "12:30"), ("13:00", "17:00")]
    }

    # Philip cannot meet Wednesday
    eligible_days = ["Monday", "Tuesday", "Thursday"]

    for day in eligible_days:
        # Convert busy times to minutes from 9:00
        laura_busy_min = []
        for s, e in laura_busy[day]:
            add_busy(laura_busy_min, s, e)

        philip_busy_min = []
        for s, e in philip_busy[day]:
            add_busy(philip_busy_min, s, e)

        laura_free = find_free_slots(laura_busy_min, 0, work_end - work_start)
        philip_free = find_free_slots(philip_busy_min, 0, work_end - work_start)

        common = intersect_slots(laura_free, philip_free, duration)
        if common:
            start_min = common[0][0] + work_start
            end_min = start_min + duration
            start_time = min_to_time(start_min)
            end_time = min_to_time(end_min)
            print(f"{day}:{start_time}:{end_time}")
            return

    print("No suitable slot found")

if __name__ == "__main__":
    main()