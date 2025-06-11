from z3 import *

def main():
    # Initialize solver and variables
    s = Solver()
    day = Int('day')
    start = Int('start')
    
    # Day must be 0 (Monday) or 1 (Tuesday)
    s.add(day >= 0, day <= 1)
    # Start time must be between 0 and 450 minutes (9:00 to 16:30)
    s.add(start >= 0, start <= 450)
    
    # Busy intervals in minutes relative to 9:00
    bobby_monday = [[330, 360]]  # 14:30 to 15:00
    bobby_tuesday = [[0, 150], [180, 210], [240, 360], [390, 480]]  # 9:00-11:30, 12:00-12:30, 13:00-15:00, 15:30-17:00
    michael_monday = [[0, 60], [90, 270], [300, 360], [390, 480]]  # 9:00-10:00, 10:30-13:30, 14:00-15:00, 15:30-17:00
    michael_tuesday = [[0, 90], [120, 150], [180, 300], [360, 420], [450, 480]]  # 9:00-10:30, 11:00-11:30, 12:00-14:00, 15:00-16:00, 16:30-17:00
    
    # Add constraints for Bobby
    for b_start, b_end in bobby_monday:
        s.add(Implies(day == 0, Or(start + 30 <= b_start, start >= b_end))
    for b_start, b_end in bobby_tuesday:
        s.add(Implies(day == 1, Or(start + 30 <= b_start, start >= b_end))
    
    # Add constraints for Michael
    for m_start, m_end in michael_monday:
        s.add(Implies(day == 0, Or(start + 30 <= m_start, start >= m_end)))
    for m_start, m_end in michael_tuesday:
        s.add(Implies(day == 1, Or(start + 30 <= m_start, start >= m_end)))
    
    # Optimize for the earliest time
    opt = Optimize()
    opt.add(s.assertions())
    absolute = day * 1440 + start  # Total minutes from Monday 9:00
    opt.minimize(absolute)
    
    if opt.check() == sat:
        m = opt.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Convert start_val to time string
        total_minutes = start_val
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_min = minutes
        start_time = f"{start_hour:02d}:{start_min:02d}"
        
        # Calculate end time
        end_minutes = total_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_min = end_minutes % 60
        end_time = f"{end_hour:02d}:{end_min:02d}"
        
        day_str = "Monday" if d_val == 0 else "Tuesday"
        print(f"Meet on {day_str} from {start_time} to {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()