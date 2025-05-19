def time_to_min(t):
    hours, mins = map(int, t.split(':'))
    return hours * 60 + mins

def min_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Define work hours and meeting duration
work_start = time_to_min('09:00')
work_end = time_to_min('17:00')
meeting_duration = 30

# Define each person's busy intervals in minutes
busy_times = {
    'Kimberly': [(time_to_min('10:00'), time_to_min('10:30')),
                 (time_to_min('11:00'), time_to_min('12:00')),
                 (time_to_min('16:00'), time_to_min('16:30'))],
    'Megan': [],  # No meetings, but avoid before 10:00
    'Marie': [(time_to_min('10:00'), time_to_min('11:00')),
              (time_to_min('11:30'), time_to_min('15:00')),
              (time_to_min('16:00'), time_to_min('16:30'))],
    'Diana': [(time_to_min('09:30'), time_to_min('10:00')),
              (time_to_min('10:30'), time_to_min('14:30')),
              (time_to_min('15:30'), time_to_min('17:00'))]
}

# Check slots from 10:00 (Megan's preference) onwards
for start in range(time_to_min('10:00'), work_end - meeting_duration + 1):
    end = start + meeting_duration
    valid = True
    
    # Check Kimberly's availability
    for s, e in busy_times['Kimberly']:
        if not (end <= s or start >= e):
            valid = False
            break
    if not valid:
        continue
    
    # Check Megan's constraint (start >= 10:00 is already enforced by loop range)
    
    # Check Marie's availability
    for s, e in busy_times['Marie']:
        if not (end <= s or start >= e):
            valid = False
            break
    if not valid:
        continue
    
    # Check Diana's availability
    for s, e in busy_times['Diana']:
        if not (end <= s or start >= e):
            valid = False
            break
    if not valid:
        continue
    
    # If all checks passed
    print(f"Monday:{min_to_time(start)}:{min_to_time(end)}")
    break