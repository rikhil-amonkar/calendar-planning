from z3 import *

def main():
    # Start time in minutes from 9:00
    s = Int('s')
    
    # Work hours: 9:00 (0 min) to 17:00 (480 min)
    # Meeting must start between 0 and 450 (inclusive) to end by 480
    constraints = [s >= 0, s <= 450]
    
    # Busy times in minutes from 9:00
    cynthia_busy = [
        (30, 90),    # 9:30-10:30
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (360, 420)   # 15:00-16:00
    ]
    
    lauren_busy = [
        (0, 30),     # 9:00-9:30
        (90, 120),   # 10:30-11:00
        (150, 180),  # 11:30-12:00
        (240, 270),  # 13:00-13:30
        (300, 330),  # 14:00-14:30
        (360, 390),  # 15:00-15:30
        (420, 480)   # 16:00-17:00
    ]
    
    robert_busy = [
        (90, 120),   # 10:30-11:00
        (150, 180),  # 11:30-12:00
        (210, 270),  # 12:30-13:30
        (300, 420)   # 14:00-16:00
    ]
    
    # Add constraints for each participant's busy intervals
    for start_busy, end_busy in cynthia_busy:
        constraints.append(Or(s + 30 <= start_busy, s >= end_busy))
        
    for start_busy, end_busy in lauren_busy:
        constraints.append(Or(s + 30 <= start_busy, s >= end_busy))
        
    for start_busy, end_busy in robert_busy:
        constraints.append(Or(s + 30 <= start_busy, s >= end_busy))
    
    # Create solver and minimize start time
    opt = Optimize()
    opt.add(constraints)
    opt.minimize(s)
    
    if opt.check() == sat:
        m = opt.model()
        start_min = m.eval(s).as_long()
        # Convert start time to HH:MM
        start_hour = 9 + start_min // 60
        start_minute = start_min % 60
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        
        # Calculate end time
        end_min = start_min + 30
        end_hour = 9 + end_min // 60
        end_minute = end_min % 60
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        # Output the meeting details
        print("Monday")
        print(start_time)
        print(end_time)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()