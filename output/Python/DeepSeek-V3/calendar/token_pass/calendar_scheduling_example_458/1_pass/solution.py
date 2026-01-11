def time_to_minutes(t):
    """Convert HH:MM to minutes since 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes since 9:00 to HH:MM."""
    h = 9 + m // 60
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def main():
    # Work hours
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    
    # Duration in minutes
    duration = 30
    
    # Busy intervals for each person (in minutes since 9:00)
    busy_intervals = {
        "Wayne": [],  # free all day, but preference handled separately
        "Melissa": [(time_to_minutes("10:00"), time_to_minutes("11:00")),
                    (time_to_minutes("12:30"), time_to_minutes("14:00")),
                    (time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Catherine": [],
        "Gregory": [(time_to_minutes("12:30"), time_to_minutes("13:00")),
                    (time_to_minutes("15:30"), time_to_minutes("16:00"))],
        "Victoria": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                     (time_to_minutes("10:30"), time_to_minutes("11:30")),
                     (time_to_minutes("13:00"), time_to_minutes("14:00")),
                     (time_to_minutes("14:30"), time_to_minutes("15:00")),
                     (time_to_minutes("15:30"), time_to_minutes("16:30"))],
        "Thomas": [(time_to_minutes("10:00"), time_to_minutes("12:00")),
                   (time_to_minutes("12:30"), time_to_minutes("13:00")),
                   (time_to_minutes("14:30"), time_to_minutes("16:00"))],
        "Jennifer": [(time_to_minutes("9:00"), time_to_minutes("9:30")),
                     (time_to_minutes("10:00"), time_to_minutes("10:30")),
                     (time_to_minutes("11:00"), time_to_minutes("13:00")),
                     (time_to_minutes("13:30"), time_to_minutes("14:30")),
                     (time_to_minutes("15:00"), time_to_minutes("15:30")),
                     (time_to_minutes("16:00"), time_to_minutes("16:30"))]
    }
    
    # Wayne's preference: avoid before 14:00
    wayne_pref_start = time_to_minutes("14:00")
    
    # Generate all possible start times (in minute increments)
    possible_starts = []
    for start in range(work_start, work_end - duration + 1):
        # Check Wayne's preference
        if start < wayne_pref_start:
            continue
        # Check each person's busy intervals
        conflict = False
        for person, intervals in busy_intervals.items():
            for busy_start, busy_end in intervals:
                # Check if meeting overlaps with busy interval
                if not (start + duration <= busy_start or start >= busy_end):
                    conflict = True
                    break
            if conflict:
                break
        if not conflict:
            possible_starts.append(start)
    
    # Output the first available slot
    if possible_starts:
        start_time = possible_starts[0]
        end_time = start_time + duration
        start_str = minutes_to_time(start_time)
        end_str = minutes_to_time(end_time)
        print(f"Monday")
        print(f"{start_str}:{end_str}")
    else:
        print("No suitable time found.")

if __name__ == "__main__":
    main()