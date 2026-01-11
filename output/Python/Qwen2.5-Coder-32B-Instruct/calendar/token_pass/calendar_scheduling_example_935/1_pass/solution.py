def parse_busy_times(busy_str):
    """Convert a string of busy times into a list of tuples."""
    busy_times = busy_str.split(', ')
    return [tuple(map(int, t.split(':'))) for t in busy_times]

def find_free_slots(busy_times, work_start=9, work_end=17, interval=30):
    """Find free slots in a day given busy times."""
    free_slots = []
    current_time = work_start * 60  # Convert to minutes for easier calculation
    work_end_minutes = work_end * 60
    
    for busy_start, busy_end in busy_times:
        busy_start_minutes = busy_start * 60
        busy_end_minutes = busy_end * 60
        
        if current_time < busy_start_minutes:
            free_slots.append((current_time, busy_start_minutes))
        
        current_time = max(current_time, busy_end_minutes)
    
    if current_time < work_end_minutes:
        free_slots.append((current_time, work_end_minutes))
    
    # Convert back to hours and minutes
    free_slots_hours = [(s // 60, s % 60, e // 60, e % 60) for s, e in free_slots]
    return free_slots_hours

def find_common_slots(terry_free, frances_free):
    """Find common free slots between Terry and Frances."""
    common_slots = []
    for t_start_h, t_start_m, t_end_h, t_end_m in terry_free:
        for f_start_h, f_start_m, f_end_h, f_end_m in frances_free:
            # Calculate overlap
            overlap_start_h = max(t_start_h, f_start_h)
            overlap_start_m = max(t_start_m, f_start_m)
            overlap_end_h = min(t_end_h, f_end_h)
            overlap_end_m = min(t_end_m, f_start_m + (f_end_m >= f_start_m + 30))
            
            if overlap_start_h < overlap_end_h or (overlap_start_h == overlap_end_h and overlap_start_m < overlap_end_m):
                common_slots.append((overlap_start_h, overlap_start_m, overlap_end_h, overlap_end_m))
    return common_slots

def filter_and_sort_slots(slots, day):
    """Filter out Tuesday slots and sort the rest."""
    if day == 'Tuesday':
        return []
    return sorted(slots)

def main():
    terry_busy_str = "10:30 to 11:00, 12:30 to 14:00, 15:00 to 17:00, 9:30 to 10:00, 10:30 to 11:00, 14:00 to 14:30, 16:00 to 16:30, 9:30 to 10:30, 11:00 to 12:00, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00, 9:30 to 10:00, 12:00 to 12:30, 13:00 to 14:30, 16:00 to 16:30, 9:00 to 11:30, 12:00 to 12:30, 13:30 to 16:00, 16:30 to 17:00"
    frances_busy_str = "9:30 to 11:00, 11:30 to 13:00, 14:00 to 14:30, 15:00 to 16:00, 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:00, 13:00 to 14:30, 15:30 to 16:30, 9:30 to 10:00, 10:30 to 11:00, 11:30 to 16:00, 16:30 to 17:00, 11:00 to 12:30, 14:30 to 17:00, 9:30 to 10:30, 11:00 to 12:30, 13:00 to 16:00, 16:30 to 17:00"
    
    days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
    terry_busy = {day: [] for day in days}
    frances_busy = {day: [] for day in days}
    
    for day, busy in zip(days, terry_busy_str.split(';')):
        terry_busy[day] = parse_busy_times(busy.strip())
    
    for day, busy in zip(days, frances_busy_str.split(';')):
        frances_busy[day] = parse_busy_times(busy.strip())
    
    all_slots = []
    for day in days:
        terry_free = find_free_slots(terry_busy[day])
        frances_free = find_free_slots(frances_busy[day])
        common_slots = find_common_slots(terry_free, frances_free)
        filtered_slots = filter_and_sort_slots(common_slots, day)
        all_slots.extend([(slot, day) for slot in filtered_slots])
    
    # Sort all slots by time and day priority (Tuesday last)
    all_slots.sort(key=lambda x: (x[0][0], x[0][1], days.index(x[1])))
    
    if all_slots:
        best_slot, best_day = all_slots[0]
        print(f"{best_slot[0]:02}:{best_slot[1]:02}:{best_slot[2]:02}:{best_slot[3]:02} {best_day}")
    else:
        print("No available slot found.")

main()