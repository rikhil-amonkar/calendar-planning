def time_to_minutes(t):
    hours, minutes = map(int, t.split(':'))
    return hours * 60 + minutes

def minutes_to_time(m):
    return f"{m // 60:02d}:{m % 60:02d}"

# Work hours and constraints
work_hours = {"Tuesday": (time_to_minutes("09:00"), time_to_minutes("17:00"))}

# Margaret's availability (Tuesday after 14:30, excluding existing blocks)
margaret_blocks = {"Tuesday": [(time_to_minutes("12:00"), time_to_minutes("12:30"))]}
margaret_available = []
for day in ["Tuesday"]:
    day_start = time_to_minutes("14:30")  # Constraint: Tuesday before 14:30 excluded
    day_end = work_hours[day][1]
    margaret_available.append((day, day_start, day_end))

# Alexis's schedule processing
alexis_blocks = {
    "Tuesday": [
        ("09:00", "09:30"),
        ("10:00", "10:30"),
        ("14:00", "16:30")
    ]
}

# Find available slots for Alexis on Tuesday
alexis_available = []
for day in ["Tuesday"]:
    work_start, work_end = work_hours[day]
    current_start = work_start
    # Convert blocks to minutes and sort
    blocks = sorted([(time_to_minutes(s), time_to_minutes(e)) for s, e in alexis_blocks[day]])
    for block_start, block_end in blocks:
        if current_start < block_start:
            alexis_available.append((day, current_start, block_start))
        current_start = max(current_start, block_end)
    if current_start < work_end:
        alexis_available.append((day, current_start, work_end))

# Find overlapping slots
solution_found = False
for m_day, m_start, m_end in margaret_available:
    for a_day, a_start, a_end in alexis_available:
        if m_day == a_day:
            overlap_start = max(m_start, a_start)
            overlap_end = min(m_end, a_end)
            if overlap_end - overlap_start >= 30:
                print(f"{m_day} {minutes_to_time(overlap_start)}:{minutes_to_time(overlap_end)}")
                solution_found = True
                exit()

if not solution_found:
    print("No solution found")