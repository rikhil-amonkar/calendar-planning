import z3

def main():
    # Define the variables
    day = z3.Int('day')
    start_minutes = z3.Int('start_minutes')
    
    # Meeting duration in minutes
    duration = 60
    
    # Work hours: 9:00 to 17:00 (480 minutes from 0:00, but we offset from 9:00 -> 0)
    min_start = 0
    max_start = 480 - duration  # 420 minutes (17:00 is 480, so last start at 420)
    
    # Hard constraints for day and start time
    hard_constraints = [
        day >= 0,
        day <= 2,
        start_minutes >= min_start,
        start_minutes <= max_start
    ]
    
    # Blocked times for Judith and Timothy converted to minutes from 9:00
    # Judith's blocked times
    judith_blocked = [
        (0, 180, 210),   # Monday 12:00-12:30 (180 to 210)
        (2, 150, 180)    # Wednesday 11:30-12:00 (150 to 180)
    ]
    
    # Timothy's blocked times
    timothy_blocked = [
        (0, 30, 60),     # Monday 9:30-10:00
        (0, 90, 150),    # Monday 10:30-11:30
        (0, 210, 300),   # Monday 12:30-14:00
        (0, 390, 480),   # Monday 15:30-17:00
        (1, 30, 240),    # Tuesday 9:30-13:00
        (1, 270, 300),   # Tuesday 13:30-14:00
        (1, 330, 480),   # Tuesday 14:30-17:00
        (2, 0, 30),      # Wednesday 9:00-9:30
        (2, 90, 120),    # Wednesday 10:30-11:00
        (2, 270, 330),   # Wednesday 13:30-14:30
        (2, 360, 390),   # Wednesday 15:00-15:30
        (2, 420, 450)    # Wednesday 16:00-16:30
    ]
    
    # Add non-overlap constraints for blocked times
    for d, low, high in judith_blocked + timothy_blocked:
        # Meeting does not overlap if it's on another day OR it avoids the blocked interval
        hard_constraints.append(
            z3.Or(
                day != d,
                z3.Or(start_minutes >= high, start_minutes + duration <= low)
            )
        )
    
    # Preferences (soft constraints)
    soft_constraints = [
        day != 0,  # Avoid Monday
        z3.Implies(day == 2, start_minutes >= 180)  # On Wednesday, avoid before 12:00 (180 minutes from 9:00)
    ]
    
    # Solver with preferences
    solver_pref = z3.Solver()
    solver_pref.add(hard_constraints)
    solver_pref.add(soft_constraints)
    
    # Check with preferences first
    if solver_pref.check() == z3.sat:
        model = solver_pref.model()
    else:
        # Fallback to without preferences
        solver_no_pref = z3.Solver()
        solver_no_pref.add(hard_constraints)
        if solver_no_pref.check() == z3.sat:
            model = solver_no_pref.model()
        else:
            print("No solution found")
            return
    
    # Get the values from the model
    day_val = model[day].as_long()
    start_val = model[start_minutes].as_long()
    
    # Convert day number to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]
    
    # Calculate start and end times
    start_hour = 9 + start_val // 60
    start_minute = start_val % 60
    end_minutes = start_val + duration
    end_hour = 9 + end_minutes // 60
    end_minute = end_minutes % 60
    
    # Format the time string
    time_str = f"{start_hour:02d}:{start_minute:02d}:{end_hour:02d}:{end_minute:02d}"
    
    # Output the result
    print(f"{day_name} {time_str}")

if __name__ == "__main__":
    main()