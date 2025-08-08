def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def get_free_intervals(busy_intervals, work_start, work_end):
    free_intervals = []
    busy_intervals = sorted(busy_intervals, key=lambda x: x[0])
    current = work_start
    for start, end in busy_intervals:
        if start > current:
            free_intervals.append((current, start))
        current = max(current, end)
    if current < work_end:
        free_intervals.append((current, work_end))
    return free_intervals

def intersect_intervals(list1, list2, duration):
    # returns any interval [start, start+duration] that fits in the intersection
    for start1, end1 in list1:
        for start2, end2 in list2:
            start = max(start1, start2)
            end = min(end1, end2)
            if end - start >= duration:
                return (start, start + duration)
    return None

def main():
    # Work hours: 09:00 to 17:00 in minutes.
    work_start = 9 * 60      # 540 minutes (09:00)
    work_end = 17 * 60       # 1020 minutes (17:00)
    meeting_duration = 60    # meeting duration in minutes

    # Busy times for Laura (times in minutes)
    laura_busy = {
        "Monday": [(10*60+30, 11*60), (12*60+30, 13*60), (14*60+30, 15*60+30), (16*60, 17*60)],
        "Tuesday": [(9*60+30, 10*60), (11*60, 11*60+30), (13*60, 13*60+30), (14*60+30, 15*60), (16*60, 17*60)],
        "Wednesday": [(11*60+30, 12*60), (12*60+30, 13*60), (15*60+30, 16*60+30)],
        "Thursday": [(10*60+30, 11*60), (12*60, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    }

    # Busy times for Philip (times in minutes)
    philip_busy = {
        "Monday": [(9*60, 17*60)],
        "Tuesday": [(9*60, 11*60), (11*60+30, 12*60), (13*60, 13*60+30), (14*60, 14*60+30), (15*60, 16*60+30)],
        "Wednesday": [(9*60, 10*60), (11*60, 12*60), (12*60+30, 16*60), (16*60+30, 17*60)],
        "Thursday": [(9*60, 10*60+30), (11*60, 12*60+30), (13*60, 17*60)]
    }

    # Days allowed (Monday, Tuesday, Wednesday, Thursday) but Philip cannot meet on Wednesday.
    days = ["Monday", "Tuesday", "Wednesday", "Thursday"]

    for day in days:
        if day == "Wednesday":
            continue  # Skip Wednesday since Philip cannot meet then.
        laura_free = get_free_intervals(laura_busy.get(day, []), work_start, work_end)
        philip_free = get_free_intervals(philip_busy.get(day, []), work_start, work_end)
        meeting_slot = intersect_intervals(laura_free, philip_free, meeting_duration)
        if meeting_slot:
            start, end = meeting_slot
            print(day, f"{minutes_to_time(start)}:{minutes_to_time(end)}")
            return
    print("No available meeting slot found.")

if __name__ == "__main__":
    main()