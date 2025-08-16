import z3

terry_busy = {
    0: [(90, 120), (210, 300), (360, 480)],
    1: [(90, 120), (150, 180), (300, 330), (420, 450)],
    2: [(90, 150), (180, 240), (270, 300), (360, 420), (450, 480)],
    3: [(90, 120), (210, 240), (270, 450), (420, 450)],
    4: [(0, 150), (240, 270), (330, 390), (450, 480)],
}

frances_busy = {
    0: [(30, 120), (150, 240), (300, 330), (360, 420)],
    1: [(0, 30), (60, 90), (120, 180), (240, 330), (390, 450)],
    2: [(30, 60), (90, 120), (150, 420), (450, 480)],
    3: [(120, 210), (330, 480)],
    4: [(30, 90), (120, 210), (240, 390), (450, 480)],
}

days_order = [0, 2, 3, 4, 1]  # Monday, Wednesday, Thursday, Friday, Tuesday

for current_day in days_order:
    start = z3.Int('start')
    s = z3.Optimize()
    s.add(start >= 0, start <= 450)
    
    # Add Terry's constraints
    for (b_start, b_end) in terry_busy.get(current_day, []):
        s.add(z3.Or(start + 30 <= b_start, start >= b_end))
    
    # Add Frances's constraints
    for (b_start, b_end) in frances_busy.get(current_day, []):
        s.add(z3.Or(start + 30 <= b_start, start >= b_end))
    
    s.minimize(start)
    
    if s.check() == z3.sat:
        model = s.model()
        start_minutes = model[start].as_long()
        
        # Convert to day name
        day_name = ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"][current_day]
        
        # Calculate start time
        start_h = 9 + (start_minutes // 60)
        start_m = start_minutes % 60
        
        # End time
        end_minutes = start_minutes + 30
        end_h = 9 + (end_minutes // 60)
        end_m = end_minutes % 60
        
        # Format as HH:MM
        start_str = f"{start_h:02d}:{start_m:02d}"
        end_str = f"{end_h:02d}:{end_m:02d}"
        
        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
        exit()