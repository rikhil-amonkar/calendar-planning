def find_meeting_time():
    # Define the work hours
    work_hours = {
        "Monday": (9, 17),
        "Tuesday": (9, 17),
        "Wednesday": (9, 17)
    }

    # Define busy intervals for Joshua and Joyce in minutes since midnight
    # Joshua's busy times
    joshua_busy = {
        "Monday": [(15*60, 15*60+30)],  # 15:00-15:30
        "Tuesday": [(11*60+30, 12*60),   # 11:30-12:00
                    (13*60, 13*60+30),   # 13:00-13:30
                    (14*60+30, 15*60)],  # 14:30-15:00
        "Wednesday": []
    }

    # Joyce's busy times
    joyce_busy = {
        "Monday": [(9*60, 9*60+30),      # 9:00-9:30
                   (10*60, 11*60),       # 10:00-11:00
                   (11*60+30, 12*60+30), # 11:30-12:30
                   (13*60, 15*60),       # 13:00-15:00
                   (15*60+30, 17*60)],   # 15:30-17:00
        "Tuesday": [(9*60, 17*60)],      # 9:00-17:00
        "Wednesday": [(9*60, 9*60+30),   # 9:00-9:30
                      (10*60, 11*60),    # 10:00-11:00
                      (12*60+30, 15*60+30), # 12:30-15:30
                      (16*60, 16*60+30)] # 16:00-16:30
    }

    # Joyce prefers not to meet on Monday before 12:00
    def joyce_available(day, start_time, end_time):
        if day == "Monday" and start_time < 12*60:
            return False
        return True

    # Function to get free intervals for a person
    def get_free_intervals(busy, day, work_start, work_end):
        free = []
        current = work_start
        for busy_start, busy_end in busy[day]:
            if busy_start > current:
                free.append((current, busy_start))
            current = max(current, busy_end)
        if current < work_end:
            free.append((current, work_end))
        return free

    # Convert minutes back to HH:MM format
    def format_time(minutes):
        return f"{minutes//60:02d}:{minutes%60:02d}"

    # Check each day
    for day in ["Monday", "Tuesday", "Wednesday"]:
        work_start, work_end = work_hours[day]
        work_start *= 60
        work_end *= 60

        # Get free intervals for Joshua and Joyce
        joshua_free = get_free_intervals(joshua_busy, day, work_start, work_end)
        joyce_free = get_free_intervals(joyce_busy, day, work_start, work_end)

        # Find common free intervals
        common_free = []
        for j_start, j_end in joshua_free:
            for q_start, q_end in joyce_free:
                overlap_start = max(j_start, q_start)
                overlap_end = min(j_end, q_end)
                if overlap_start < overlap_end:
                    common_free.append((overlap_start, overlap_end))

        # Look for a 30-minute slot
        for start, end in common_free:
            if end - start >= 30:
                # Check Joyce's preference
                if joyce_available(day, start, end):
                    # Convert to HH:MM format
                    start_formatted = format_time(start)
                    end_formatted = format_time(end)
                    return f"{day} {start_formatted}-{end_formatted}"

    return "No common free time found"

print(find_meeting_time())