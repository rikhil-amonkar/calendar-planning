def find_time_slot():
    import datetime

    # Define work hours (9:00 to 17:00)
    work_start = 9 * 60
    work_end = 17 * 60

    # Define participants' schedules in minutes since midnight
    # Format: {day: [busy_intervals]}
    jean_busy = {
        'Tuesday': [(11*60 +30, 12*60), (16*60, 16*60 +30)]
    }

    doris_busy = {
        'Monday': [(9*60, 11*60 +30), (12*60, 12*60 +30), 
                   (13*60 +30, 16*60), (16*60 +30, 17*60)],
        'Tuesday': [(9*60, 17*60)]
    }

    # Check days in order: Monday first
    for day in ['Monday', 'Tuesday']:
        # Skip Tuesday as Doris is fully booked
        if day == 'Tuesday':
            continue

        # Generate all possible 30-minute slots on this day
        for start_min in range(work_start, work_end - 30 + 1, 30):
            end_min = start_min + 30

            # Check Jean's availability (free on Monday)
            jean_available = True
            if day == 'Tuesday':
                # Check Jean's Tuesday schedule
                for (busy_start, busy_end) in jean_busy.get(day, []):
                    if not (end_min <= busy_start or start_min >= busy_end):
                        jean_available = False
                        break

            # Check Doris's availability
            doris_available = True
            for (busy_start, busy_end) in doris_busy.get(day, []):
                if not (end_min <= busy_start or start_min >= busy_end):
                    doris_available = False
                    break

            # Apply Doris's preference (avoid Monday after 14:00)
            if day == 'Monday' and start_min >= 14 * 60:
                continue  # Skip slots after 14:00

            if jean_available and doris_available:
                # Format time to HH:MM
                def format_time(mins):
                    return f"{mins//60:02d}:{mins%60:02d}"

                time_slot = (
                    f"{format_time(start_min)}:{format_time(end_min)}"
                )
                return (day, time_slot)

    return None  # Shouldn't reach here per problem statement

day, time_slot = find_time_slot()
start, end = time_slot.split(':')
print(f"{day} {start}:{end}")