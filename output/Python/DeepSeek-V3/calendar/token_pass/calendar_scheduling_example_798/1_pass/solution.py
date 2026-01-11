def time_to_minutes(t):
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    m = m % 60
    return f"{h:02d}:{m:02d}"

def add_busy(busy_dict, day, start_str, end_str):
    start_min = time_to_minutes(start_str) - 9*60  # relative to 9:00
    end_min = time_to_minutes(end_str) - 9*60
    busy_dict[day].append((start_min, end_min))

def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = []
    current_start, current_end = sorted_intervals[0]
    for start, end in sorted_intervals[1:]:
        if start <= current_end:
            current_end = max(current_end, end)
        else:
            merged.append((current_start, current_end))
            current_start, current_end = start, end
    merged.append((current_start, current_end))
    return merged

def find_free_slots(busy_times, work_start_min, work_end_min, duration_min):
    free_slots = []
    last_end = work_start_min
    for start, end in busy_times:
        if start > last_end and start - last_end >= duration_min:
            free_slots.append((last_end, start))
        last_end = max(last_end, end)
    if work_end_min - last_end >= duration_min:
        free_slots.append((last_end, work_end_min))
    return free_slots

def main():
    days = ["Monday", "Tuesday", "Wednesday"]
    work_start = "9:00"
    work_end = "17:00"
    duration_min = 30
    
    work_start_min = time_to_minutes(work_start) - time_to_minutes("9:00")
    work_end_min = time_to_minutes(work_end) - time_to_minutes("9:00")
    
    # Busy times relative to 9:00
    nancy_busy = {day: [] for day in days}
    jose_busy = {day: [] for day in days}
    
    # Nancy
    add_busy(nancy_busy, "Monday", "10:00", "10:30")
    add_busy(nancy_busy, "Monday", "11:30", "12:30")
    add_busy(nancy_busy, "Monday", "13:30", "14:00")
    add_busy(nancy_busy, "Monday", "14:30", "15:30")
    add_busy(nancy_busy, "Monday", "16:00", "17:00")
    
    add_busy(nancy_busy, "Tuesday", "9:30", "10:30")
    add_busy(nancy_busy, "Tuesday", "11:00", "11:30")
    add_busy(nancy_busy, "Tuesday", "12:00", "12:30")
    add_busy(nancy_busy, "Tuesday", "13:00", "13:30")
    add_busy(nancy_busy, "Tuesday", "15:30", "16:00")
    
    add_busy(nancy_busy, "Wednesday", "10:00", "11:30")
    add_busy(nancy_busy, "Wednesday", "13:30", "16:00")
    
    # Jose
    add_busy(jose_busy, "Monday", "9:00", "17:00")
    add_busy(jose_busy, "Tuesday", "9:00", "17:00")
    add_busy(jose_busy, "Wednesday", "9:00", "9:30")
    add_busy(jose_busy, "Wednesday", "10:00", "12:30")
    add_busy(jose_busy, "Wednesday", "13:30", "14:30")
    add_busy(jose_busy, "Wednesday", "15:00", "17:00")
    
    # Find earliest slot
    for day in days:
        combined_busy = nancy_busy[day] + jose_busy[day]
        merged_busy = merge_intervals(combined_busy)
        free_slots = find_free_slots(merged_busy, work_start_min, work_end_min, duration_min)
        if free_slots:
            slot_start, slot_end = free_slots[0]
            # Convert back to absolute time
            start_abs = slot_start + time_to_minutes("9:00")
            end_abs = start_abs + duration_min
            start_str = minutes_to_time(start_abs)
            end_str = minutes_to_time(end_abs)
            print(f"{day}:{start_str}:{end_str}")
            return
    
    print("No slot found")

if __name__ == "__main__":
    main()