from datetime import datetime, timedelta

def parse_time(t_str):
    return datetime.strptime(t_str, "%H:%M")

def time_to_str(t):
    return t.strftime("%H:%M")

def schedule_meeting(work_start, work_end, duration, margaret_blocks, donna_blocks, helen_meetings, helen_no_after):
    # Convert all to datetime objects for today (date irrelevant)
    base_date = datetime.today().date()
    work_start = datetime.combine(base_date, parse_time(work_start).time())
    work_end = datetime.combine(base_date, parse_time(work_end).time())
    helen_no_after_time = datetime.combine(base_date, parse_time(helen_no_after).time())
    
    # Convert blocked times to datetime ranges
    def parse_blocks(block_list):
        blocks = []
        for b in block_list:
            start_str, end_str = b.split(" to ")
            start = datetime.combine(base_date, parse_time(start_str).time())
            end = datetime.combine(base_date, parse_time(end_str).time())
            blocks.append((start, end))
        return blocks
    
    margaret_blocks_dt = parse_blocks(margaret_blocks)
    donna_blocks_dt = parse_blocks(donna_blocks)
    helen_meetings_dt = parse_blocks(helen_meetings)
    
    # Generate free slots for each person
    def free_slots(blocks, start_bound, end_bound):
        # blocks are busy times
        slots = []
        current = start_bound
        for busy_start, busy_end in sorted(blocks, key=lambda x: x[0]):
            if current < busy_start:
                slots.append((current, busy_start))
            current = max(current, busy_end)
        if current < end_bound:
            slots.append((current, end_bound))
        return slots
    
    # Margaret's free slots
    margaret_free = free_slots(margaret_blocks_dt, work_start, work_end)
    donna_free = free_slots(donna_blocks_dt, work_start, work_end)
    
    # Helen's free slots: first get free before no-after time, then intersect with work hours
    helen_free_before_no_after = free_slots(helen_meetings_dt, work_start, min(work_end, helen_no_after_time))
    
    # Intersect all three
    possible_slots = []
    for m_start, m_end in margaret_free:
        for d_start, d_end in donna_free:
            for h_start, h_end in helen_free_before_no_after:
                start = max(m_start, d_start, h_start)
                end = min(m_end, d_end, h_end)
                if start < end and (end - start) >= timedelta(minutes=duration):
                    possible_slots.append((start, end))
    
    if not possible_slots:
        return None
    
    # Pick earliest slot
    chosen_slot = min(possible_slots, key=lambda x: x[0])
    return chosen_slot

# Input data
work_start = "9:00"
work_end = "17:00"
duration = 30
margaret_blocks = [
    "9:00 to 10:00",
    "10:30 to 11:00",
    "11:30 to 12:00",
    "13:00 to 13:30",
    "15:00 to 15:30"
]
donna_blocks = [
    "14:30 to 15:00",
    "16:00 to 16:30"
]
helen_meetings = [
    "9:00 to 9:30",
    "10:00 to 11:30",
    "13:00 to 14:00",
    "14:30 to 15:00",
    "15:30 to 17:00"
]
helen_no_after = "13:30"

slot = schedule_meeting(work_start, work_end, duration,
                        margaret_blocks, donna_blocks,
                        helen_meetings, helen_no_after)

if slot:
    start_time, end_time = slot
    # Output in HH:MM:HH:MM format and day
    print(f"Monday {start_time.strftime('%H:%M')}:{end_time.strftime('%H:%M')}")
else:
    print("No suitable slot found")