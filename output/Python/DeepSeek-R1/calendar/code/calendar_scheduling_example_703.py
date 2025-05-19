def main():
    from datetime import time

    def minutes_to_time(m):
        return time(hour=m // 60, minute=m % 60)

    # Define participants' schedules and constraints
    days = ['Monday', 'Tuesday', 'Wednesday']
    stephanie_busy = {
        'Monday': [(570, 600), (630, 660), (690, 720), (840, 870)],
        'Tuesday': [(720, 780)],
        'Wednesday': [(540, 600), (780, 840)]
    }
    betty_busy = {
        'Monday': [(540, 600), (660, 690), (870, 900), (930, 960)],
        'Tuesday': [(540, 570), (690, 720), (750, 870)],  # Post-12:30 blocked by constraint
        'Wednesday': [(600, 690), (720, 840), (870, 1020)]
    }

    # Check each day in preferred order (Tuesday, Wednesday, Monday)
    for day in ['Tuesday', 'Wednesday', 'Monday']:
        # Adjust Betty's availability based on Tuesday constraint
        work_start, work_end = 540, 1020
        betty_work_end = work_end
        if day == 'Tuesday':
            betty_work_end = 750  # 12:30 in minutes

        # Calculate free slots for Stephanie
        st_free = []
        prev_end = work_start
        for start, end in sorted(stephanie_busy.get(day, [])):
            if start > prev_end:
                st_free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < work_end:
            st_free.append((prev_end, work_end))

        # Calculate free slots for Betty
        bt_free = []
        prev_end = work_start
        for start, end in sorted([(s, e) for s, e in betty_busy.get(day, []) if s < betty_work_end]):
            if start > prev_end:
                bt_free.append((prev_end, start))
            prev_end = max(prev_end, end)
        if prev_end < betty_work_end:
            bt_free.append((prev_end, betty_work_end))

        # Find overlapping free slots of at least 60 minutes
        overlap = []
        i = j = 0
        while i < len(st_free) and j < len(bt_free)):
            s_start, s_end = st_free[i]
            b_start, b_end = bt_free[j]
            start = max(s_start, b_start)
            end = min(s_end, b_end)
            if start < end:
                if end - start >= 60:
                    overlap.append((start, start + 60))
                    break  # Take earliest possible slot
                # Move the pointer which ends earlier
                if s_end < b_end:
                    i += 1
                else:
                    j += 1
            else:
                if s_start < b_start:
                    i += 1
                else:
                    j += 1
        if overlap:
            start, end = overlap[0]
            print(f"{day}:{minutes_to_time(start).strftime('%H:%M')}-{minutes_to_time(end).strftime('%H:%M')}")
            return

if __name__ == "__main__":
    main()