def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

work_hours = (9*60, 17*60)
days = ['Monday', 'Tuesday']

ryan_schedule = {
    'Monday': [('9:30', '10:00'), ('11:00', '12:00'), ('13:00', '13:30'), ('15:30', '16:00')],
    'Tuesday': [('11:30', '12:30'), ('15:30', '16:00')]
}

adam_schedule = {
    'Monday': [('9:00', '10:30'), ('11:00', '13:30'), ('14:00', '16:00'), ('16:30', '17:00')],
    'Tuesday': [('9:00', '10:00'), ('10:30', '15:30'), ('16:00', '17:00')]
}

adam_preferences = {'Monday': (14*60 + 30, None)}

def get_busy_intervals(day):
    ryan = [tuple(parse_time(t) for t in interval) for interval in ryan_schedule.get(day, [])]
    adam = [tuple(parse_time(t) for t in interval) for interval in adam_schedule.get(day, [])]
    merged = sorted(ryan + adam, key=lambda x: x[0])
    if not merged:
        return []
    intervals = [merged[0]]
    for current in merged[1:]:
        last = intervals[-1]
        if current[0] <= last[1]:
            intervals[-1] = (last[0], max(last[1], current[1]))
        else:
            intervals.append(current)
    return intervals

def find_slot():
    for day in days:
        start_adjust = adam_preferences.get(day, (0, None))[0] if day == 'Monday' else 0
        day_start = max(work_hours[0], start_adjust)
        busy = get_busy_intervals(day)
        free_start = day_start
        for start, end in busy:
            if start > free_start:
                if end - free_start >= 30:
                    slot_end = free_start + 30
                    return day, format_time(free_start), format_time(slot_end)
            free_start = max(free_start, end)
        if work_hours[1] - free_start >= 30:
            slot_end = free_start + 30
            return day, format_time(free_start), format_time(slot_end)
    return None

day, start, end = find_slot()
print(f"{day} {start.replace(':','')}:{end.replace(':','')}")