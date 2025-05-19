def time_to_minutes(time):
    hours, minutes = map(int, time.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

def compute_free_intervals(busy_schedule, work_start, work_end):
    busy_schedule.sort()
    free_intervals = []
    current_start = work_start
    for start, end in busy_schedule:
        if start > current_start:
            free_intervals.append((current_start, start))
        current_start = max(current_start, end)
    if current_start < work_end:
        free_intervals.append((current_start, work_end))
    return free_intervals

# Participant schedules and preferences
larry_schedule = {}
samuel_schedule = {
    'Monday': [('10:30', '11:00'), ('12:00', '12:30'), ('13:00', '15:00'), ('15:30', '16:30')],
    'Tuesday': [('9:00', '12:00'), ('14:00', '15:30'), ('16:30', '17:00')],
    'Wednesday': [('10:30', '11:00'), ('11:30', '12:00'), ('12:30', '13:00'), ('14:00', '14:30'), ('15:00', '16:00')]
}

# Convert schedules to minutes
samuel_busy = {}
for day, meetings in samuel_schedule.items():
    samuel_busy[day] = [(time_to_minutes(start), time_to_minutes(end)) for start, end in meetings]

work_hours = (9*60, 17*60)
duration = 30
days_order = ['Monday', 'Tuesday', 'Wednesday']

# Process preferences
avoid_days = set()
larry_preferences = ['would rather not meet on Wednesday']
samuel_preferences = ['would like to avoid more meetings on Tuesday']

if 'would rather not meet on Wednesday' in larry_preferences:
    avoid_days.add('Wednesday')
if 'would like to avoid more meetings on Tuesday' in samuel_preferences:
    avoid_days.add('Tuesday')

# Find earliest possible slot
found = False
for day in days_order:
    if day in avoid_days:
        continue
    
    work_start, work_end = work_hours
    busy = samuel_busy.get(day, [])
    free_intervals = compute_free_intervals(busy, work_start, work_end)
    
    possible_slots = []
    for interval in free_intervals:
        start, end = interval
        current_start = start
        while current_start + duration <= end:
            possible_slots.append((current_start, current_start + duration))
            current_start += 1  # Check every minute
    
    if possible_slots:
        possible_slots.sort()
        chosen_start, chosen_end = possible_slots[0]
        start_time = minutes_to_time(chosen_start)
        end_time = minutes_to_time(chosen_end)
        print(f"{day}:{start_time}:{end_time}")
        found = True
        break

if not found:
    print("No suitable time found")