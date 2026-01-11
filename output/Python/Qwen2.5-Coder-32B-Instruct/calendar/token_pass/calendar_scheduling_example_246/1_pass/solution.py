from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, '%H:%M')

def generate_time_slots(start_time, end_time, interval_minutes):
    current_time = start_time
    time_slots = []
    while current_time < end_time:
        next_time = current_time + timedelta(minutes=interval_minutes)
        time_slots.append((current_time, next_time))
        current_time = next_time
    return time_slots

def mark_busy_times(busy_intervals, time_slots):
    busy_slots = set()
    for start_busy, end_busy in busy_intervals:
        for start_slot, end_slot in time_slots:
            if start_slot < end_busy and end_slot > start_busy:
                busy_slots.add((start_slot, end_slot))
    return busy_slots

def find_free_slots(time_slots, busy_slots):
    free_slots = set(time_slots) - busy_slots
    return list(free_slots)

def format_time_slot(slot):
    start, end = slot
    return f"{start.strftime('%H:%M')}:{end.strftime('%H:%M')}"

# Define workday start and end times
workday_start = parse_time('09:00')
workday_end = parse_time('17:00')
interval_minutes = 30

# Generate all possible 30-minute time slots
time_slots = generate_time_slots(workday_start, workday_end, interval_minutes)

# Define busy times for each participant
busy_times = {
    'Jacob': [(parse_time('13:30'), parse_time('14:00')), (parse_time('14:30'), parse_time('15:00'))],
    'Diana': [(parse_time('09:30'), parse_time('10:00')), (parse_time('11:30'), parse_time('12:00')),
              (parse_time('13:00'), parse_time('13:30')), (parse_time('16:00'), parse_time('16:30'))],
    'Adam': [(parse_time('09:30'), parse_time('10:30')), (parse_time('11:00'), parse_time('12:30')),
             (parse_time('15:30'), parse_time('16:00'))],
    'Angela': [(parse_time('09:30'), parse_time('10:00')), (parse_time('10:30'), parse_time('12:00')),
               (parse_time('13:00'), parse_time('15:30')), (parse_time('16:00'), parse_time('16:30'))],
    'Dennis': [(parse_time('09:00'), parse_time('09:30')), (parse_time('10:30'), parse_time('11:30')),
               (parse_time('13:00'), parse_time('15:00')), (parse_time('16:30'), parse_time('17:00'))]
}

# Mark all busy times across all participants
all_busy_slots = set()
for person, intervals in busy_times.items():
    all_busy_slots.update(mark_busy_times(intervals, time_slots))

# Find free slots
free_slots = find_free_slots(time_slots, all_busy_slots)

# Select the first available free slot
if free_slots:
    selected_slot = free_slots[0]
    print(f"Meeting time: {format_time_slot(selected_slot)}, Day: Monday")
else:
    print("No available time slot found.")