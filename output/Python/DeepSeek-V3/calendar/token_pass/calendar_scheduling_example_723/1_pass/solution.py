def time_to_minutes(t):
    """Convert HH:MM to minutes since 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes since 9:00 to HH:MM."""
    h = 9 + m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def add_busy(busy, day, start, end):
    busy[day].append((time_to_minutes(start), time_to_minutes(end)))

def find_slot(busy1, busy2, day, duration=30, work_start=0, work_end=480):
    """Find earliest slot of given duration on given day for two people."""
    # Combine and sort busy intervals
    busy = sorted(busy1[day] + busy2[day])
    free_start = work_start
    for start, end in busy:
        if start > free_start and start - free_start >= duration:
            return free_start, free_start + duration
        free_start = max(free_start, end)
    if work_end - free_start >= duration:
        return free_start, free_start + duration
    return None

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    # Busy times stored as list of (start_min, end_min) for each day
    arthur_busy = {day: [] for day in days}
    michael_busy = {day: [] for day in days}

    # Arthur's meetings
    add_busy(arthur_busy, "Monday", "11:00", "11:30")
    add_busy(arthur_busy, "Monday", "13:30", "14:00")
    add_busy(arthur_busy, "Monday", "15:00", "15:30")
    # Tuesday: Arthur cannot meet anyway, skip adding meetings
    add_busy(arthur_busy, "Wednesday", "10:00", "10:30")
    add_busy(arthur_busy, "Wednesday", "11:00", "11:30")
    add_busy(arthur_busy, "Wednesday", "12:00", "12:30")
    add_busy(arthur_busy, "Wednesday", "14:00", "14:30")
    add_busy(arthur_busy, "Wednesday", "16:00", "16:30")

    # Michael's meetings
    add_busy(michael_busy, "Monday", "9:00", "12:00")
    add_busy(michael_busy, "Monday", "12:30", "13:00")
    add_busy(michael_busy, "Monday", "14:00", "14:30")
    add_busy(michael_busy, "Monday", "15:00", "17:00")
    # Tuesday irrelevant
    add_busy(michael_busy, "Wednesday", "10:00", "12:30")
    add_busy(michael_busy, "Wednesday", "13:00", "13:30")

    # Arthur cannot meet Tuesday
    days_to_check = ["Monday", "Wednesday"]
    duration = 30
    work_start = 0      # 9:00
    work_end = 480      # 17:00

    for day in days_to_check:
        slot = find_slot(arthur_busy, michael_busy, day, duration, work_start, work_end)
        if slot:
            start_min, end_min = slot
            start_time = minutes_to_time(start_min)
            end_time = minutes_to_time(end_min)
            print(f"{day}:{start_time}:{end_time}")
            return

if __name__ == "__main__":
    main()