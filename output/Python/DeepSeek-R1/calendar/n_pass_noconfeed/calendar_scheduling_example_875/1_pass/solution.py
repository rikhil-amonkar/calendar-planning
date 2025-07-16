def main():
    base_minutes = 9 * 60  # 540 minutes (absolute for 9:00)
    natalie_schedule_str = "Monday during 9:00 to 9:30, 10:00 to 12:00, 12:30 to 13:00, 14:00 to 14:30, 15:00 to 16:30; Tuesday during 9:00 to 9:30, 10:00 to 10:30, 12:30 to 14:00, 16:00 to 17:00; Wednesday during 11:00 to 11:30, 16:00 to 16:30; Thursday during 10:00 to 11:00, 11:30 to 15:00, 15:30 to 16:00, 16:30 to 17:00"
    william_schedule_str = "Monday during 9:30 to 11:00, 11:30 to 17:00; Tuesday during 9:00 to 13:00, 13:30 to 16:00; Wednesday during 9:00 to 12:30, 13:00 to 14:30, 15:30 to 16:00, 16:30 to 17:00; Thursday during 9:00 to 10:30, 11:00 to 11:30, 12:00 to 12:30, 13:00 to 14:00, 15:00 to 17:00"

    def parse_schedule(schedule_str):
        schedule = {}
        day_parts = schedule_str.split(';')
        for part in day_parts:
            part = part.strip()
            if not part:
                continue
            if "during" not in part:
                continue
            day, intervals_str = part.split("during", 1)
            day = day.strip()
            intervals_list = []
            interval_strs = [s.strip() for s in intervals_str.split(',')]
            for interval in interval_strs:
                if not interval:
                    continue
                if " to " not in interval:
                    continue
                start_str, end_str = interval.split(" to ", 1)
                start_str = start_str.strip()
                end_str = end_str.strip()
                start_parts = start_str.split(':')
                start_abs = int(start_parts[0]) * 60 + int(start_parts[1])
                start_rel = start_abs - base_minutes
                end_parts = end_str.split(':')
                end_abs = int(end_parts[0]) * 60 + int(end_parts[1])
                end_rel = end_abs - base_minutes
                intervals_list.append((start_rel, end_rel))
            schedule[day] = intervals_list
        return schedule

    natalie_schedule = parse_schedule(natalie_schedule_str)
    william_schedule = parse_schedule(william_schedule_str)
    days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']

    def compute_free_intervals(busy_intervals):
        if not busy_intervals:
            return [(0, 480)]
        busy_sorted = sorted(busy_intervals, key=lambda x: x[0])
        free = []
        current = 0
        for start, end in busy_sorted:
            if current < start:
                free.append((current, start))
            current = max(current, end)
        if current < 480:
            free.append((current, 480))
        return free

    for day in days:
        natalie_busy = natalie_schedule.get(day, [])
        william_busy = william_schedule.get(day, [])
        natalie_free = compute_free_intervals(natalie_busy)
        william_free = compute_free_intervals(william_busy)
        common_free = []
        i = j = 0
        while i < len(natalie_free) and j < len(william_free):
            a_low, a_high = natalie_free[i]
            b_low, b_high = william_free[j]
            low = max(a_low, b_low)
            high = min(a_high, b_high)
            if low < high:
                common_free.append((low, high))
            if a_high < b_high:
                i += 1
            else:
                j += 1
        for start, end in common_free:
            if end - start >= 60:
                meeting_start = start
                meeting_end = start + 60
                start_abs = meeting_start + base_minutes
                end_abs = meeting_end + base_minutes
                start_hh = start_abs // 60
                start_mm = start_abs % 60
                end_hh = end_abs // 60
                end_mm = end_abs % 60
                time_str = f"{start_hh:02d}:{start_mm:02d}:{end_hh:02d}:{end_mm:02d}"
                print(day)
                print(time_str)
                return
    print("No meeting time found")

if __name__ == "__main__":
    main()