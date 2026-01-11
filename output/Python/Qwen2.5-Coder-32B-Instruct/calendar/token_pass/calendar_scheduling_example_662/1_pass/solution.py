def find_meeting_time(gary_schedule, david_schedule, meeting_duration=60, work_start=9*60, work_end=17*60):
    def parse_schedule(schedule):
        parsed = {'Monday': [], 'Tuesday': []}
        for entry in schedule.split(';'):
            day, times = entry.split(' during ')
            start, end = map(lambda x: int(x.split(':')[0]) * 60 + int(x.split(':')[1]), times.split(' to '))
            parsed[day.strip()].append((start, end))
        return parsed

    def find_free_slots(day_schedule, work_start, work_end):
        free_slots = []
        current_time = work_start
        for start, end in sorted(day_schedule):
            if current_time < start:
                free_slots.append((current_time, min(end, work_end)))
            current_time = max(current_time, end)
        if current_time < work_end:
            free_slots.append((current_time, work_end))
        return free_slots

    def find_common_slot(gary_free, david_free, meeting_duration):
        for g_start, g_end in gary_free:
            for d_start, d_end in david_free:
                overlap_start = max(g_start, d_start)
                overlap_end = min(g_end, d_end)
                if overlap_end - overlap_start >= meeting_duration:
                    return overlap_start, overlap_start + meeting_duration
        return None

    gary_parsed = parse_schedule(gary_schedule)
    david_parsed = parse_schedule(david_schedule)

    for day in ['Monday', 'Tuesday']:
        gary_free = find_free_slots(gary_parsed[day], work_start, work_end)
        david_free = find_free_slots(david_parsed[day], work_start, work_end)
        common_slot = find_common_slot(gary_free, david_free, meeting_duration)
        if common_slot:
            start_hour, start_minute = divmod(common_slot[0], 60)
            end_hour, end_minute = divmod(common_slot[1], 60)
            return f"{start_hour:02}:{start_minute:02}:{end_hour:02}:{end_minute:02} {day}"

gary_schedule = "Gary has blocked their calendar on Monday during 9:30 to 10:00, 11:00 to 13:00, 14:00 to 14:30, 16:30 to 17:00, Tuesday during 9:00 to 9:30, 10:30 to 11:00, 14:30 to 16:00"
david_schedule = "David has blocked their calendar on Monday during 9:00 to 9:30, 10:00 to 13:00, 14:30 to 16:30, Tuesday during 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:30, 13:00 to 14:30, 15:00 to 16:00, 16:30 to 17:00"

print(find_meeting_time(gary_schedule, david_schedule))