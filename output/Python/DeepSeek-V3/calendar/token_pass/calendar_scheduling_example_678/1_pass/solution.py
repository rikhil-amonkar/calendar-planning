def time_to_minutes(t):
    """Convert HH:MM to minutes from 00:00."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    """Convert minutes from 00:00 to HH:MM."""
    return f"{m // 60:02d}:{m % 60:02d}"

def busy_to_free(busy_list, day_start, day_end):
    """Convert list of busy intervals to free intervals within work hours."""
    free = []
    busy_sorted = sorted(busy_list, key=lambda x: x[0])
    current = day_start
    for start, end in busy_sorted:
        if current < start:
            free.append((current, start))
        current = max(current, end)
    if current < day_end:
        free.append((current, day_end))
    return free

def intersect_free(free1, free2):
    """Intersect two lists of free intervals."""
    i, j = 0, 0
    res = []
    while i < len(free1) and j < len(free2):
        start = max(free1[i][0], free2[j][0])
        end = min(free1[i][1], free2[j][1])
        if start < end:
            res.append((start, end))
        if free1[i][1] < free2[j][1]:
            i += 1
        else:
            j += 1
    return res

def find_slot(russell_busy, alexander_busy, pref_no_before, duration_min=60):
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    days = ["Monday", "Tuesday"]
    
    # Define busy times in minutes from 00:00 for each day
    # We'll store as (day_start_min, day_end_min, list_of_busy)
    day_schedules = {
        "Monday": (work_start, work_end),
        "Tuesday": (work_start, work_end),
    }
    
    # Convert busy times to minutes from 00:00 for easier handling
    russell_busy_min = {
        "Monday": [(time_to_minutes("10:30"), time_to_minutes("11:00"))],
        "Tuesday": [(time_to_minutes("13:00"), time_to_minutes("13:30"))],
    }
    alexander_busy_min = {
        "Monday": [
            (time_to_minutes("9:00"), time_to_minutes("11:30")),
            (time_to_minutes("12:00"), time_to_minutes("14:30")),
            (time_to_minutes("15:00"), time_to_minutes("17:00"))
        ],
        "Tuesday": [
            (time_to_minutes("9:00"), time_to_minutes("10:00")),
            (time_to_minutes("13:00"), time_to_minutes("14:00")),
            (time_to_minutes("15:00"), time_to_minutes("15:30")),
            (time_to_minutes("16:00"), time_to_minutes("16:30"))
        ],
    }
    
    for day in days:
        day_start, day_end = day_schedules[day]
        russell_free = busy_to_free(russell_busy_min[day], day_start, day_end)
        alexander_free = busy_to_free(alexander_busy_min[day], day_start, day_end)
        
        common_free = intersect_free(russell_free, alexander_free)
        
        # Apply Russell's preference for Tuesday
        if day == "Tuesday":
            pref_min = time_to_minutes(pref_no_before)
            filtered_free = []
            for start, end in common_free:
                if end <= pref_min:
                    continue  # entirely before preference, skip
                if start < pref_min:
                    start = pref_min
                if start < end:
                    filtered_free.append((start, end))
            common_free = filtered_free
        
        # Find duration_min slot
        for start, end in common_free:
            if end - start >= duration_min:
                slot_start = start
                slot_end = slot_start + duration_min
                return day, minutes_to_time(slot_start), minutes_to_time(slot_end)
    
    return None

if __name__ == "__main__":
    # Russell's preference: not before 13:30 on Tuesday
    result = find_slot(None, None, "13:30", 60)
    if result:
        day, start, end = result
        print(f"{day}")
        print(f"{start}:{end}")
    else:
        print("No suitable slot found")