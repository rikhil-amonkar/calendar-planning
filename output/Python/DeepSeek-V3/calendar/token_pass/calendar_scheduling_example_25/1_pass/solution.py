def main():
    # Given data
    work_start = 9 * 60  # 9:00 in minutes from midnight
    work_end = 17 * 60   # 17:00
    duration = 60

    # Busy times in minutes from 9:00
    anthony_busy = [(30, 60), (180, 240), (420, 450)]
    pamela_busy = [(30, 60), (450, 480)]
    zachary_busy = [(0, 150), (180, 210), (240, 270), (330, 360), (420, 480)]

    # Pamela's extra constraint: cannot end after 14:30
    pamela_limit = 14 * 60 + 30  # 14:30 in minutes from midnight
    # Convert to minutes from 9:00: 14:30 - 9:00 = 5h30 = 330 minutes
    pamela_limit_from_start = 330

    # Find free slots for each person within work hours
    def free_slots(busy_list, start, end):
        busy_sorted = sorted(busy_list, key=lambda x: x[0])
        free = []
        current = start
        for b_start, b_end in busy_sorted:
            if current < b_start:
                free.append((current, b_start))
            current = max(current, b_end)
        if current < end:
            free.append((current, end))
        return free

    anthony_free = free_slots(anthony_busy, 0, 480)
    pamela_free = free_slots(pamela_busy, 0, 480)
    zachary_free = free_slots(zachary_busy, 0, 480)

    # Find intersection of free slots
    possible_slots = []
    for a_start, a_end in anthony_free:
        for p_start, p_end in pamela_free:
            for z_start, z_end in zachary_free:
                # Find overlap of these three intervals
                overlap_start = max(a_start, p_start, z_start)
                overlap_end = min(a_end, p_end, z_end)
                if overlap_end - overlap_start >= duration:
                    # Check Pamela's constraint: meeting end <= 330 minutes from 9:00
                    if overlap_start + duration <= pamela_limit_from_start:
                        possible_slots.append((overlap_start, overlap_end))

    # Choose earliest slot
    if possible_slots:
        # Sort by start time
        possible_slots.sort(key=lambda x: x[0])
        best_start = possible_slots[0][0]
        best_end = best_start + duration

        # Convert back to HH:MM
        def to_time(minutes_from_9):
            total_minutes = 9 * 60 + minutes_from_9
            h = total_minutes // 60
            m = total_minutes % 60
            return f"{h:02d}:{m:02d}"

        start_str = to_time(best_start)
        end_str = to_time(best_end)

        print(f"Monday {start_str}:{end_str}")
    else:
        print("No suitable slot found")

if __name__ == "__main__":
    main()