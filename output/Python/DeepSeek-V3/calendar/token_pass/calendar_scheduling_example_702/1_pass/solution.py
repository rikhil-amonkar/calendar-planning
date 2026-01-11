from datetime import datetime, timedelta

def time_to_minutes(t):
    """Convert 'HH:MM' to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to 'HH:MM'."""
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def parse_schedule(schedule_text, day):
    """
    schedule_text format: 'Monday during 11:00 to 11:30, 14:00 to 14:30, ...'
    Returns list of (start_minute, end_minute) for that day.
    """
    lines = schedule_text.split(';')
    busy = []
    for line in lines:
        if day in line:
            # Extract times
            parts = line.strip().split('during ')[1]
            periods = parts.split(', ')
            for p in periods:
                if 'to' in p:
                    start_str, end_str = p.split(' to ')
                    start_min = time_to_minutes(start_str)
                    end_min = time_to_minutes(end_str)
                    busy.append((start_min, end_min))
    return busy

def free_slots(busy, work_start_min, work_end_min):
    """Given busy intervals in minutes, return free intervals."""
    busy_sorted = sorted(busy, key=lambda x: x[0])
    free = []
    current = work_start_min
    for start, end in busy_sorted:
        if start > current:
            free.append((current, start))
        current = max(current, end)
    if current < work_end_min:
        free.append((current, work_end_min))
    return free

def intersect_slots(slots1, slots2):
    """Intersect two lists of free intervals."""
    i, j = 0, 0
    result = []
    while i < len(slots1) and j < len(slots2):
        start = max(slots1[i][0], slots2[j][0])
        end = min(slots1[i][1], slots2[j][1])
        if start < end:
            result.append((start, end))
        if slots1[i][1] < slots2[j][1]:
            i += 1
        else:
            j += 1
    return result

def main():
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    meeting_duration = 30  # minutes

    # Busy schedules as given
    robert_schedule = """
    Monday during 11:00 to 11:30, 14:00 to 14:30, 15:30 to 16:00,
    Tuesday during 10:30 to 11:00, 15:00 to 15:30,
    Wednesday during 10:00 to 11:00, 11:30 to 12:00, 12:30 to 13:00, 13:30 to 14:00, 15:00 to 15:30, 16:00 to 16:30
    """
    ralph_schedule = """
    Monday during 10:00 to 13:30, 14:00 to 14:30, 15:00 to 17:00,
    Tuesday during 9:00 to 9:30, 10:00 to 10:30, 11:00 to 11:30, 12:00 to 13:00, 14:00 to 15:30, 16:00 to 17:00,
    Wednesday during 10:30 to 11:00, 11:30 to 12:00, 13:00 to 14:30, 16:30 to 17:00
    """

    days = ["Tuesday", "Wednesday", "Monday"]  # Tuesday first (Robert avoids Monday)

    for day in days:
        robert_busy = parse_schedule(robert_schedule, day)
        ralph_busy = parse_schedule(ralph_schedule, day)

        robert_free = free_slots(robert_busy, work_start, work_end)
        ralph_free = free_slots(ralph_busy, work_start, work_end)

        common_free = intersect_slots(robert_free, ralph_free)

        for start, end in common_free:
            if end - start >= meeting_duration:
                meeting_start = start
                meeting_end = start + meeting_duration
                print(f"{day}:{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
                return

if __name__ == "__main__":
    main()