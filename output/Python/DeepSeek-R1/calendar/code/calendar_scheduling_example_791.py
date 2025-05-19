def find_meeting_time():
    days = ["Monday", "Tuesday", "Wednesday"]
    nicole_busy = {
        "Monday": [(9, 0, 9, 30), (13, 0, 13, 30), (14, 30, 15, 30)],
        "Tuesday": [(9, 0, 9, 30), (11, 30, 13, 30), (14, 30, 15, 30)],
        "Wednesday": [(10, 0, 11, 0), (12, 30, 15, 0), (16, 0, 17, 0)]
    }
    ruth_busy = {
        "Monday": [(9, 0, 17, 0)],
        "Tuesday": [(9, 0, 17, 0)],
        "Wednesday": [(9, 0, 10, 30), (11, 0, 11, 30), (12, 0, 12, 30), (13, 30, 15, 30), (16, 0, 16, 30)]
    }
    ruth_preference = {"Wednesday": (13, 30)}

    for day in days:
        if day == "Wednesday":
            ruth_end_pref = ruth_preference["Wednesday"][0] * 60 + ruth_preference["Wednesday"][1]
        else:
            ruth_end_pref = 17 * 60
        
        ruth_slots = []
        ruth_blocked = ruth_busy[day]
        ruth_blocked_sorted = sorted(ruth_blocked, key=lambda x: x[0]*60 + x[1])
        current_start = 9 * 60
        for block in ruth_blocked_sorted:
            block_start = block[0] * 60 + block[1]
            block_end = block[2] * 60 + block[3]
            if current_start < block_start:
                ruth_slots.append((current_start, block_start))
            current_start = max(current_start, block_end)
        if current_start < 17 * 60:
            ruth_slots.append((current_start, 17 * 60))
        
        nicole_slots = []
        nicole_blocked = nicole_busy[day]
        nicole_blocked_sorted = sorted(nicole_blocked, key=lambda x: x[0]*60 + x[1])
        current_start = 9 * 60
        for block in nicole_blocked_sorted:
            block_start = block[0] * 60 + block[1]
            block_end = block[2] * 60 + block[3]
            if current_start < block_start:
                nicole_slots.append((current_start, block_start))
            current_start = max(current_start, block_end)
        if current_start < 17 * 60:
            nicole_slots.append((current_start, 17 * 60))
        
        for ruth_start, ruth_end in ruth_slots:
            if day == "Wednesday":
                ruth_end = min(ruth_end, ruth_end_pref)
            for nicole_start, nicole_end in nicole_slots:
                overlap_start = max(ruth_start, nicole_start)
                overlap_end = min(ruth_end, nicole_end)
                if overlap_end - overlap_start >= 30:
                    start_h = overlap_start // 60
                    start_m = overlap_start % 60
                    end_h = (overlap_start + 30) // 60
                    end_m = (overlap_start + 30) % 60
                    return (f"{day} {start_h:02d}:{start_m:02d}-{end_h:02d}:{end_m:02d}")

    return "No suitable time found"

result = find_meeting_time()
print(result)