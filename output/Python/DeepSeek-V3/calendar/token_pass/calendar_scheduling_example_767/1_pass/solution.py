def time_to_minutes(t):
    """Convert HH:MM to minutes from 9:00."""
    h, m = map(int, t.split(':'))
    return (h - 9) * 60 + m

def minutes_to_time(m):
    """Convert minutes from 9:00 to HH:MM."""
    h = m // 60 + 9
    mm = m % 60
    return f"{h:02d}:{mm:02d}"

def merge_intervals(intervals):
    """Merge overlapping intervals."""
    if not intervals:
        return []
    intervals.sort(key=lambda x: x[0])
    merged = [intervals[0]]
    for start, end in intervals[1:]:
        last_start, last_end = merged[-1]
        if start <= last_end:
            merged[-1] = (last_start, max(last_end, end))
        else:
            merged.append((start, end))
    return merged

def find_free_slot(busy, day_start, day_end, duration):
    """Find a free slot of given duration in minutes."""
    free_start = day_start
    for start, end in busy:
        if free_start + duration <= start:
            return free_start, free_start + duration
        free_start = max(free_start, end)
    if free_start + duration <= day_end:
        return free_start, free_start + duration
    return None

def main():
    # Work hours: 9:00 to 17:00 -> 0 to 480 minutes
    day_start = 0
    day_end = 480
    duration = 60  # 1 hour
    
    # Blocked times in minutes from 9:00
    martha = {
        "Monday": [(time_to_minutes("16:00"), time_to_minutes("17:00"))],
        "Tuesday": [(time_to_minutes("15:00"), time_to_minutes("15:30"))],
        "Wednesday": [
            (time_to_minutes("10:00"), time_to_minutes("11:00")),
            (time_to_minutes("14:00"), time_to_minutes("14:30"))
        ]
    }
    
    beverly = {
        "Monday": [
            (time_to_minutes("9:00"), time_to_minutes("13:30")),
            (time_to_minutes("14:00"), time_to_minutes("17:00"))
        ],
        "Tuesday": [(time_to_minutes("9:00"), time_to_minutes("17:00"))],
        "Wednesday": [
            (time_to_minutes("9:30"), time_to_minutes("15:30")),
            (time_to_minutes("16:30"), time_to_minutes("17:00"))
        ]
    }
    
    days = ["Monday", "Tuesday", "Wednesday"]
    
    for day in days:
        # Combine busy intervals for both people
        busy = martha.get(day, []) + beverly.get(day, [])
        busy = merge_intervals(busy)
        
        # Find free slot
        slot = find_free_slot(busy, day_start, day_end, duration)
        if slot:
            start_min, end_min = slot
            start_time = minutes_to_time(start_min)
            end_time = minutes_to_time(end_min)
            print(f"{day}")
            print(f"{start_time}:{end_time}")
            return
    
    print("No suitable slot found.")

if __name__ == "__main__":
    main()