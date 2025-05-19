from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def time_range(start, end):
    return (start.hour, start.minute), (end.hour, end.minute)

def get_available_slots(busy_slots, day_start, day_end):
    slots = []
    prev_end = day_start
    for start, end in sorted(busy_slots):
        if prev_end < start:
            slots.append((prev_end, start))
        prev_end = max(prev_end, end)
    if prev_end < day_end:
        slots.append((prev_end, day_end))
    return slots

def find_meeting_time(diane_busy, matthew_busy, matthew_prefs, duration):
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    day_start = parse_time("09:00")
    day_end = parse_time("17:00")
    delta = timedelta(minutes=duration)

    for day_idx in range(5):
        day = days[day_idx]
        
        diane_day = [time_range(parse_time(s.split()[0]), parse_time(s.split()[2])) for s in diane_busy[day]]
        matthew_day = [time_range(parse_time(s.split()[0]), parse_time(s.split()[2])) for s in matthew_busy[day]]
        
        diane_free = get_available_slots(diane_day, day_start, day_end)
        matthew_free = get_available_slots(matthew_day, day_start, day_end)
        
        for slot in diane_free:
            d_start, d_end = slot
            for m_slot in matthew_free:
                m_start, m_end = m_slot
                start = max(d_start, m_start)
                end = min(d_end, m_end)
                if (end - start) >= delta:
                    if day == "Wednesday" and (start < parse_time("12:30")):
                        continue
                    meeting_end = start + delta
                    return (
                        day,
                        f"{start.hour:02d}:{start.minute:02d}",
                        f"{meeting_end.hour:02d}:{meeting_end.minute:02d}"
                    )
    return None

diane_busy = {
    "Monday": ["12:00 to 12:30", "15:00 to 15:30"],
    "Tuesday": ["10:00 to 11:00", "11:30 to 12:00", "12:30 to 13:00", "16:00 to 17:00"],
    "Wednesday": ["9:00 to 9:30", "14:30 to 15:00", "16:30 to 17:00"],
    "Thursday": ["15:30 to 16:30"],
    "Friday": ["9:30 to 11:30", "14:30 to 15:00", "16:00 to 17:00"]
}

matthew_busy = {
    "Monday": ["9:00 to 10:00", "10:30 to 17:00"],
    "Tuesday": ["9:00 to 17:00"],
    "Wednesday": ["9:00 to 11:00", "12:00 to 14:30", "16:00 to 17:00"],
    "Thursday": ["9:00 to 16:00"],
    "Friday": ["9:00 to 17:00"]
}

result = find_meeting_time(diane_busy, matthew_busy, ["Wednesday"], 60)
print(f"{result[0]} {result[1]}-{result[2]}")