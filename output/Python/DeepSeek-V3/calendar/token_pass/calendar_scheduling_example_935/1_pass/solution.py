import datetime

def parse_busy_slots(busy_text):
    """
    Converts a string like "Monday during 10:30 to 11:00, 12:30 to 14:00"
    into a list of (day, start_minute, end_minute) where minutes are from 00:00.
    """
    days_map = {"Monday": 0, "Tuesday": 1, "Wednesday": 2, "Thursday": 3, "Friday": 4}
    slots = []
    lines = busy_text.strip().split(";")
    for line in lines:
        if not line.strip():
            continue
        parts = line.split(" during ")
        day_name = parts[0].strip()
        day_index = days_map[day_name]
        time_ranges = parts[1].strip().split(", ")
        for tr in time_ranges:
            start_str, end_str = tr.split(" to ")
            start_h, start_m = map(int, start_str.split(":"))
            end_h, end_m = map(int, end_str.split(":"))
            start_minutes = start_h * 60 + start_m
            end_minutes = end_h * 60 + end_m
            slots.append((day_index, start_minutes, end_minutes))
    return slots

def add_busy_to_free_matrix(free_matrix, busy_slots):
    """
    free_matrix[day][minute] = True if free, initially all True.
    Mark busy slots as False.
    """
    for day, start_m, end_m in busy_slots:
        for m in range(start_m, end_m):
            free_matrix[day][m] = False

def find_earliest_slot(free_matrix, duration_minutes, avoid_day=None):
    """
    Find earliest 30-minute slot where all minutes are free.
    If avoid_day is given, skip that day unless no other day works.
    """
    work_start = 9 * 60
    work_end = 17 * 60
    days_order = [0, 1, 2, 3, 4]
    if avoid_day is not None:
        # Try other days first, then avoided day
        days_order = [d for d in days_order if d != avoid_day] + [avoid_day]
    
    for day in days_order:
        for start in range(work_start, work_end - duration_minutes + 1):
            if all(free_matrix[day][m] for m in range(start, start + duration_minutes)):
                return day, start, start + duration_minutes
    return None

def main():
    # Participants' busy times
    terry_busy_text = """Monday during 10:30 to 11:00, 12:30 to 14:00, 15:00 to 17:00; 
    Tuesday during 9:30 to 10:00, 10:30 to 11:00, 14:00 to 14:30, 16:00 to 16:30; 
    Wednesday during 9:30 to 10:30, 11:00 to 12:00, 13:00 to 13:30, 15:00 to 16:00, 16:30 to 17:00; 
    Thursday during 9:30 to 10:00, 12:00 to 12:30, 13:00 to 14:30, 16:00 to 16:30; 
    Friday during 9:00 to 11:30, 12:00 to 12:30, 13:30 to 16:00, 16:30 to 17:00"""
    
    frances_busy_text = """Monday during 9:30 to 11:00, 11:30 to 13:00, 14:00 to 14:30, 15:00 to 16:00; 
    Tuesday during 9:00 to 9:30, 10:00 to 10:30, 11:00 to 12:00, 13:00 to 14:30, 15:30 to 16:30; 
    Wednesday during 9:30 to 10:00, 10:30 to 11:00, 11:30 to 16:00, 16:30 to 17:00; 
    Thursday during 11:00 to 12:30, 14:30 to 17:00; 
    Friday during 9:30 to 10:30, 11:00 to 12:30, 13:00 to 16:00, 16:30 to 17:00"""
    
    # Parse busy slots
    terry_busy = parse_busy_slots(terry_busy_text)
    frances_busy = parse_busy_slots(frances_busy_text)
    
    # Initialize free matrix (5 days, 24*60 minutes, but we only care 9-17)
    # We'll store from 0:00 to 23:59 for simplicity
    free_matrix = [[True] * (24*60) for _ in range(5)]
    
    # Mark non-work hours as busy
    for day in range(5):
        for minute in range(0, 9*60):
            free_matrix[day][minute] = False
        for minute in range(17*60, 24*60):
            free_matrix[day][minute] = False
    
    # Add busy times
    add_busy_to_free_matrix(free_matrix, terry_busy)
    add_busy_to_free_matrix(free_matrix, frances_busy)
    
    # Find earliest slot, avoiding Tuesday if possible (Tuesday index = 1)
    duration = 30
    result = find_earliest_slot(free_matrix, duration, avoid_day=1)
    
    if result:
        day_idx, start_m, end_m = result
        days = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
        day_name = days[day_idx]
        start_str = f"{start_m//60:02d}:{start_m%60:02d}"
        end_str = f"{end_m//60:02d}:{end_m%60:02d}"
        print(f"{day_name}")
        print(f"{start_str}:{end_str}")
    else:
        print("No slot found")

if __name__ == "__main__":
    main()