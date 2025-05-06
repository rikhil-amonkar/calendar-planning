import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# Meeting is 30 minutes long, work hours from 9:00 AM to 5:00 PM (0 to 480 minutes)
# Start time must be between 0 and 450 (since 450 + 30 = 480)
solver.add(start_time >= 0)
solver.add(start_time <= 450)

# Wayne's preference: avoid before 14:00 (300 minutes after 9:00 AM)
solver.add(start_time >= 300)

# Melissa's blocked intervals
# 10:00-11:00 (60-120)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 120))
# 12:30-14:00 (210-300)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 300))
# 15:00-15:30 (360-390)
solver.add(z3.Or(start_time + 30 <= 360, start_time >= 390))

# Gregory's blocked intervals
# 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))
# 15:30-16:00 (390-420)
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 420))

# Victoria's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 10:30-11:30 (90-150)
solver.add(z3.Or(start_time + 30 <= 90, start_time >= 150))
# 13:00-14:00 (240-300)
solver.add(z3.Or(start_time + 30 <= 240, start_time >= 300))
# 14:30-15:00 (330-360)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 360))
# 15:30-16:30 (390-450)
solver.add(z3.Or(start_time + 30 <= 390, start_time >= 450))

# Thomas's blocked intervals
# 10:00-12:00 (60-180)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 180))
# 12:30-13:00 (210-240)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 240))
# 14:30-16:00 (330-420)
solver.add(z3.Or(start_time + 30 <= 330, start_time >= 420))

# Jennifer's blocked intervals
# 9:00-9:30 (0-30)
solver.add(z3.Or(start_time + 30 <= 0, start_time >= 30))
# 10:00-10:30 (60-90)
solver.add(z3.Or(start_time + 30 <= 60, start_time >= 90))
# 11:00-13:00 (120-240)
solver.add(z3.Or(start_time + 30 <= 120, start_time >= 240))
# 13:30-14:30 (210-330)
solver.add(z3.Or(start_time + 30 <= 210, start_time >= 330))
# 15:00-15:30 (360-390)
solver.add(z3.Or(start_time + 30 <= 360, start_time >= 390))
# 16:00-16:30 (420-450)
solver.add(z3.Or(start_time + 30 <= 420, start_time >= 450))

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