def merge_intervals(intervals):
    if not intervals:
        return []
    sorted_intervals = sorted(intervals, key=lambda x: x[0])
    merged = [sorted_intervals[0]]
    for current in sorted_intervals[1:]:
        last = merged[-1]
        if current[0] <= last[1]:
            merged[-1] = (last[0], max(last[1], current[1]))
        else:
            merged.append(current)
    return merged

def minutes_to_time(m):
    hours = 9 + m // 60
    mins = m % 60
    return f"{hours:02d}:{mins:02d}"

def main():
    # Define busy intervals for each participant
    shirley = [(90, 120), (180, 210)]
    jacob = [(0, 30), (60, 90), (120, 150), (210, 270), (330, 360)]
    stephen = [(150, 180), (210, 240)]
    margaret = [(0, 30), (90, 210), (240, 270), (360, 390), (450, 480)]
    mason = [(0, 60), (90, 120), (150, 210), (240, 270), (300, 330), (450, 480)]
    
    all_busy = shirley + jacob + stephen + margaret + mason
    
    # Merge intervals
    merged = merge_intervals(all_busy)
    
    # Get free intervals within work hours (0 to 480)
    start_work = 0
    end_work = 480
    free_intervals = []
    prev_end = start_work
    for interval in merged:
        start, end = interval
        if prev_end < start:
            free_intervals.append( (prev_end, start) )
        prev_end = max(prev_end, end)
    if prev_end < end_work:
        free_intervals.append( (prev_end, end_work) )
    
    # Find the earliest valid slot
    for start, end in free_intervals:
        if end - start >= 30 and start >= 330:  # 330 is 14:30
            proposed_start = start
            proposed_end = proposed_start + 30
            start_time = minutes_to_time(proposed_start)
            end_time = minutes_to_time(proposed_end)
            print(f"{start_time}:{end_time} Monday")
            return
    
    # If not found, but problem says there is a solution
    # So this shouldn't happen
    print("No suitable time found")

if __name__ == "__main__":
    main()