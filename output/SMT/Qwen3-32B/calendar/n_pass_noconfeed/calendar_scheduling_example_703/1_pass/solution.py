import z3

def format_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours:02d}:{mins:02d}"

# Existing meetings for each participant and day
stephanie_meetings = {
    'Monday': [(570, 600), (630, 660), (690, 720), (840, 870)],
    'Tuesday': [(720, 780)],
    'Wednesday': [(540, 600), (780, 840)],
}

betty_meetings = {
    'Monday': [(540, 600), (660, 690), (870, 900), (930, 960)],
    'Tuesday': [(540, 570), (690, 720), (750, 870), (930, 960)],
    'Wednesday': [(600, 690), (720, 840), (870, 1020)],
}

# Order of days to prioritize avoiding Monday
days = ['Tuesday', 'Wednesday', 'Monday']

for day in days:
    solver = z3.Solver()
    s = z3.Int('s')
    # Work hours from 9:00 (540) to 17:00 (1020)
    solver.add(s >= 540)
    solver.add(s + 60 <= 1020)
    
    # Day-specific constraints
    if day == 'Tuesday':
        # Betty cannot meet after 12:30 (750 minutes)
        solver.add(s <= 750)
    
    # Add constraints for Stephanie's existing meetings
    for start, end in stephanie_meetings[day]:
        solver.add(z3.Or(s + 60 <= start, s >= end))
    
    # Add constraints for Betty's existing meetings
    for start, end in betty_meetings[day]:
        solver.add(z3.Or(s + 60 <= start, s >= end))
    
    if solver.check() == z3.sat:
        model = solver.model()
        start_minutes = model[s].as_long()
        end_minutes = start_minutes + 60
        start_str = format_time(start_minutes)
        end_str = format_time(end_minutes)
        print(f"{day} {start_str}:{end_str}")
        exit()

print("No solution found")