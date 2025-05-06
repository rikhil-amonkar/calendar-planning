import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Roger's preference: avoid before 12:30 (210 minutes after 9:00 AM)
solver.add(start_time >= 210)

# Kathleen's blocked intervals
# 14:30-15:30 (330-390)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 390))

# Carolyn's blocked intervals
# 12:00-12:30 (180-210)
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 210))
# 13:00-13:30 (240-270)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 270))

# Cheryl's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 10:00-11:30 (60-150)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 150))
# 12:30-13:30 (210-270)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 270))
# 14:00-17:00 (300-480)
solver.add(z3.Or(start_time + 30 <= 300, start_time >= 480))

# Virginia's blocked intervals
# 9:30-11:30 (30-150)
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 150))
# 12:00-12:30 (180-210)
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 210))
# 13:00-13:30 (240-270)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 270))
# 14:30-15:30 (330-390)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 390))
# 16:00-17:00 (420-480)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 480))

# Angela's blocked intervals
# 9:30-10:00 (30-60)
solver.add(z3.Or(start_time + 30 <= 30, start_time >= 60))
# 10:30-11:30 (90-150)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 150))
# 12:00-12:30 (180-210)
solver.add(z3.Or(start_time + 30 <= 180, start_time >= 210))
# 13:00-13:30 (240-270)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 270))
# 14:00-16:30 (300-450)
solver.add(z3.Or(start_time + 30 <= 300, start_time >= 450))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Convert to 24-hour format
    start_hour = 9 + (time_minutes // 60)
    start_min = time_minutes % 60
    end_hour = start_hour
    end_min = start_min + 30
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")