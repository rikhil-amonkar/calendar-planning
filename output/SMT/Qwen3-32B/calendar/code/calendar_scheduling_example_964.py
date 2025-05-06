import z3

# Initialize the Z3 solver
solver = z3.Solver()
start_time = z3.Int('start_time')

# The meeting is 1 hour long, so start_time must be between 480 (Tuesday 9:00 AM) and 900 (Tuesday 3:00 PM)
# since 900 + 60 = 960 (Tuesday 5:00 PM)
solver.add(start_time >= 480)
solver.add(start_time <= 900)

# Betty's blocked intervals on Tuesday (in minutes since Monday 9:00 AM)
# 9:30-10:00 (480 + 30 = 510 to 480 + 60 = 540)
solver.add(z3.Or(start_time + 60 <= 510, start_time >= 540))
# 10:30-11:00 (480 + 90 = 570 to 480 + 120 = 600)
solver.add(z3.Or(start_time + 60 <= 570, start_time >= 600))
# 12:00-12:30 (480 + 180 = 660 to 480 + 210 = 690)
solver.add(z3.Or(start_time + 60 <= 660, start_time >= 690))
# 13:30-15:00 (480 + 270 = 750 to 480 + 330 = 810)
solver.add(z3.Or(start_time + 60 <= 750, start_time >= 810))
# 16:30-17:00 (480 + 390 = 930 to 480 + 450 = 960)
solver.add(z3.Or(start_time + 60 <= 930, start_time >= 960))

# Megan's blocked intervals on Tuesday (in minutes since Monday 9:00 AM)
# 9:00-9:30 (480 to 510)
solver.add(z3.Or(start_time + 60 <= 480, start_time >= 510))
# 10:00-10:30 (480 + 60 = 540 to 480 + 90 = 570)
solver.add(z3.Or(start_time + 60 <= 540, start_time >= 570))
# 12:00-14:00 (480 + 180 = 660 to 480 + 300 = 780)
solver.add(z3.Or(start_time + 60 <= 660, start_time >= 780))
# 15:00-15:30 (480 + 300 = 780 to 480 + 330 = 810)
solver.add(z3.Or(start_time + 60 <= 780, start_time >= 810))
# 16:00-16:30 (480 + 360 = 840 to 480 + 390 = 930)
solver.add(z3.Or(start_time + 60 <= 840, start_time >= 930))

# Check for a solution
if solver.check() == z3.sat:
    model = solver.model()
    time_minutes = model[start_time].as_long()
    
    # Calculate day and time
    if 480 <= time_minutes < 960:
        day = "Tuesday"
        offset = time_minutes - 480
    else:
        day = "Unknown"
        offset = 0  # Should not happen
    
    start_hour = 9 + (offset // 60)
    start_min = offset % 60
    end_hour = start_hour
    end_min = start_min + 60
    if end_min == 60:
        end_hour += 1
        end_min = 0
    
    print(f"Start: {day} {start_hour}:{start_min:02d}, End: {end_hour}:{end_min:02d}")
else:
    print("No solution found.")