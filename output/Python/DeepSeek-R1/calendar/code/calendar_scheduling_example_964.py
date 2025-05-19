def find_meeting_time():
    # Define work hours
    work_start = 9 * 60
    work_end = 17 * 60

    # Define days to check
    days = ["Tuesday"]  # Monday and Friday excluded due to Megan's full day blocks

    # Convert schedules to minutes since midnight
    betty_busy = {
        "Tuesday": [
            (9*60+30, 10*60),
            (10*60+30, 11*60),
            (12*60, 12*60+30),
            (13*60+30, 15*60),
            (16*60+30, 17*60)
        ]
    }

    megan_busy = {
        "Tuesday": [
            (9*60, 9*60+30),
            (10*60, 10*60+30),
            (12*60, 14*60),
            (15*60, 15*60+30),
            (16*60, 16*60+30)
        ]
    }

    for day in days:
        # Generate free slots for Betty
        betty_slots = []
        prev_end = work_start
        for start, end in sorted(betty_busy[day]):
            if start > prev_end:
                betty_slots.append((prev_end, start))
            prev_end = end
        if prev_end < work_end:
            betty_slots.append((prev_end, work_end))

        # Generate free slots for Megan
        megan_slots = []
        prev_end = work_start
        for start, end in sorted(megan_busy[day]):
            if start > prev_end:
                megan_slots.append((prev_end, start))
            prev_end = end
        if prev_end < work_end:
            megan_slots.append((prev_end, work_end))

        # Find overlapping slots with 60+ minutes duration
        for b_start, b_end in betty_slots:
            for m_start, m_end in megan_slots:
                overlap_start = max(b_start, m_start)
                overlap_end = min(b_end, m_end)
                if overlap_end - overlap_start >= 60:
                    # Convert back to time
                    start_hr, start_min = divmod(overlap_start, 60)
                    end_hr, end_min = divmod(overlap_start + 60, 60)
                    return (
                        f"{start_hr:02d}:{start_min:02d}:{end_hr:02d}:{end_min:02d}",
                        day
                    )

    return None

time_slot, day = find_meeting_time()
print(f"{day} {time_slot}")