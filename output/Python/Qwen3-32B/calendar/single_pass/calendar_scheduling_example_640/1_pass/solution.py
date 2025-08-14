def get_free_intervals(busy_intervals, work_start, work_end):
    sorted_busy = sorted(busy_intervals, key=lambda x: x[0])
    free = []
    current_start = work_start
    for start, end in sorted_busy:
        if current_start < start:
            free.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free.append((current_start, work_end))
    return free

def float_time_to_str(t):
    hours = int(t)
    minutes = int((t - hours) * 60)
    return f"{hours:02d}:{minutes:02d}"

participants = {
    'Bobby': {
        'Monday': [(14.5, 15.0)],
        'Tuesday': [(9.0, 11.5), (12.0, 12.5), (13.0, 15.0), (15.5, 17.0)]
    },
    'Michael': {
        'Monday': [(9.0, 10.0), (10.5, 13.5), (14.0, 15.0), (15.5, 17.0)],
        'Tuesday': [(9.0, 10.5), (11.0, 11.5), (12.0, 14.0), (15.0, 16.0), (16.5, 17.0)]
    }
}

work_hours_start = 9.0
work_hours_end = 17.0
days = ['Monday', 'Tuesday']

possible_slots = []

for day in days:
    bobby_busy = participants['Bobby'].get(day, [])
    michael_busy = participants['Michael'].get(day, [])
    
    bobby_free = get_free_intervals(bobby_busy, work_hours_start, work_hours_end)
    michael_free = get_free_intervals(michael_busy, work_hours_start, work_hours_end)
    
    for b_start, b_end in bobby_free:
        for m_start, m_end in michael_free:
            overlap_start = max(b_start, m_start)
            overlap_end = min(b_end, m_end)
            if overlap_start < overlap_end:
                duration = overlap_end - overlap_start
                if duration >= 0.5:
                    possible_slots.append((day, overlap_start, overlap_end))

earliest_slot = None
for slot in possible_slots:
    if earliest_slot is None or slot[1] < earliest_slot[1]:
        earliest_slot = slot

day = earliest_slot[0]
start_time = float_time_to_str(earliest_slot[1])
end_time = float_time_to_str(earliest_slot[2])

print(f"{start_time.split(':')[0]}:{start_time.split(':')[1]}:{end_time.split(':')[0]}:{end_time.split(':')[1]} {day}")