def parse_time(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def format_time(minutes):
    return f"{minutes // 60:02d}:{minutes % 60:02d}"

def find_meeting_slot():
    work_start = parse_time("09:00")
    work_end = parse_time("17:00")
    duration = 30

    # Define busy intervals in minutes (Tuesday only since Monday is full for Albert)
    shirley_busy = [(parse_time("09:30"), parse_time("10:00"))]
    albert_busy = [
        (parse_time("09:30"), parse_time("11:00")),
        (parse_time("11:30"), parse_time("12:30")),
        (parse_time("13:00"), parse_time("16:00")),
        (parse_time("16:30"), parse_time("17:00"))
    ]

    # Generate free slots for both
    def get_free_slots(busy_slots, day_start, day_end):
        slots = []
        current = day_start
        for start, end in sorted(busy_slots):
            if current < start:
                slots.append((current, start))
            current = max(current, end)
        if current < day_end:
            slots.append((current, day_end))
        return slots

    shirley_free = get_free_slots(shirley_busy, work_start, work_end)
    albert_free = get_free_slots(albert_busy, work_start, work_end)

    # Find overlapping slots with preference handling
    for s_start, s_end in shirley_free:
        for a_start, a_end in albert_free:
            overlap_start = max(s_start, a_start)
            overlap_end = min(s_end, a_end)
            if overlap_end - overlap_start >= duration:
                # Check Shirley's preference for Tuesday before 10:30
                meeting_end = overlap_start + duration
                if parse_time("10:30") >= meeting_end:
                    return "Tuesday", (overlap_start, meeting_end)
                return "Tuesday", (overlap_start, overlap_start + duration)

    return None

day, (start, end) = find_meeting_slot()
print(f"{day} {format_time(start)}:{format_time(end)}")