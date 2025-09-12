import z3

# Create solver instance
solver = z3.Solver()

# Define start time variable (in minutes since 9:00 AM)
S = z3.Int('S')
E = S + 30  # Meeting duration is 30 minutes

# Work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
solver.add(z3.And(S >= 0, S <= 450))  # S must end by 450 to fit 30 min meeting

# Blocked intervals for each participant in minutes since 9:00 AM
blocked_intervals = [
    # Diane
    (30, 60),     # 9:30-10:00
    (330, 360),   # 14:30-15:00
    # Jack
    (270, 300),   # 13:30-14:00
    (330, 360),   # 14:30-15:00
    # Eugene
    (0, 60),      # 9:00-10:00
    (90, 150),    # 10:30-11:30
    (180, 330),   # 12:00-14:30
    (360, 450),   # 15:00-16:30
    # Patricia
    (30, 90),     # 9:30-10:30
    (120, 180),   # 11:00-12:00
    (210, 300),   # 12:30-14:00
    (360, 450),   # 15:00-16:30
]

# Add constraints to avoid overlaps with blocked intervals
for b_start, b_end in blocked_intervals:
    solver.add(z3.Or(E <= b_start, S >= b_end))

# Check for solution
if solver.check() == z3.sat:
    model = solver.model()
    S_val = model[S].as_long()
    
    # Convert start time to HH:MM format
    start_hours = 9 + (S_val // 60)
    start_minutes = S_val % 60
    start_time = f"{start_hours:02d}:{start_minutes:02d}"
    
    # Convert end time to HH:MM format
    end_val = S_val + 30
    end_hours = 9 + (end_val // 60)
    end_minutes = end_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    print(f"{start_time}:{end_time} Monday")
else:
    print("No solution found")