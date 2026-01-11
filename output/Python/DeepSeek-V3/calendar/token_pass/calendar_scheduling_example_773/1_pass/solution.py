def time_to_minutes(t):
    # t is string like "10:30"
    h, m = map(int, t.split(':'))
    return h * 60 + m

def minutes_to_time(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def find_free_slots(busy_intervals, day_start_min, day_end_min, duration_min):
    # busy_intervals: list of (start_min, end_min) within day
    # add boundaries
    points = [(day_start_min, day_start_min)] + busy_intervals + [(day_end_min, day_end_min)]
    # sort by start
    points.sort(key=lambda x: x[0])
    
    free_slots = []
    for i in range(len(points) - 1):
        end_current = points[i][1]
        start_next = points[i+1][0]
        gap = start_next - end_current
        if gap >= duration_min:
            free_slots.append((end_current, start_next))
    return free_slots

def main():
    # Work hours 9:00 to 17:00
    work_start = time_to_minutes("9:00")
    work_end = time_to_minutes("17:00")
    duration = 60  # minutes
    
    # Roy's schedule
    # Format: day: list of busy intervals as (start, end) in minutes from 0:00
    # But easier: store as minutes from 9:00=0
    # Let's define conversion relative to 9:00
    def parse_interval(day_time_str, interval_str):
        # interval_str like "10:00 to 11:30"
        start_str, end_str = interval_str.split(" to ")
        start_min = time_to_minutes(start_str) - work_start
        end_min = time_to_minutes(end_str) - work_start
        return (start_min, end_min)
    
    # Manually encode Roy's busy times relative to 9:00
    roy_busy = {
        "Monday": [
            (60, 150),   # 10:00-11:30
            (180, 240),  # 12:00-13:00
            (300, 330),  # 14:00-14:30
            (360, 480),  # 15:00-17:00
        ],
        "Tuesday": [
            (90, 150),   # 10:30-11:30
            (180, 330),  # 12:00-14:30
            (360, 390),  # 15:00-15:30
            (420, 480),  # 16:00-17:00
        ],
        "Wednesday": [
            (30, 150),   # 9:30-11:30
            (210, 300),  # 12:30-14:00
            (330, 390),  # 14:30-15:30
            (450, 480),  # 16:30-17:00
        ]
    }
    
    days_order = ["Monday", "Tuesday", "Wednesday"]
    
    # Find earliest slot
    for day in days_order:
        free_slots = find_free_slots(roy_busy[day], 0, work_end - work_start, duration)
        if free_slots:
            # earliest slot that day
            slot_start, slot_end = free_slots[0]
            # Convert back to absolute time
            abs_start = work_start + slot_start
            abs_end = work_start + slot_end
            # We only need 1 hour, so take slot_start to slot_start + duration
            # but free_slots already ensures length >= duration, we take earliest start
            meeting_start = abs_start
            meeting_end = meeting_start + duration
            print(f"{day}")
            print(f"{minutes_to_time(meeting_start)}:{minutes_to_time(meeting_end)}")
            return

if __name__ == "__main__":
    main()