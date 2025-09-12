from z3 import *

def main():
    # Create solver
    s = Solver()
    
    # Define variables: day (0=Mon, 1=Tue, 2=Wed) and start time in minutes from 9:00
    day = Int('day')
    start = Int('start')
    duration = 30  # Meeting duration in minutes
    
    # Work hours: 9:00 to 17:00 (480 minutes total)
    min_time = 0
    max_time = 480 - duration
    
    # Constrain day to 0, 1, or 2
    s.add(day >= 0, day <= 2)
    s.add(start >= min_time, start <= max_time)
    
    # Nicole's busy intervals in minutes from 9:00
    nicole_busy = [
        [(0, 30), (240, 270), (330, 390)],   # Monday
        [(0, 30), (150, 270), (330, 390)],   # Tuesday
        [(60, 120), (210, 360), (420, 480)]  # Wednesday
    ]
    
    # Ruth's busy intervals in minutes from 9:00
    ruth_busy = [
        [(0, 480)],                           # Monday
        [(0, 480)],                           # Tuesday
        [(0, 90), (120, 150), (180, 210), (270, 330), (420, 450)]  # Wednesday
    ]
    
    # Ruth's constraint: No meeting on Wednesday after 13:30 (270 minutes from 9:00)
    s.add(Implies(day == 2, start + duration <= 270))
    
    # Function to check overlap with busy intervals
    def no_overlap(busy_list, d, s_time):
        constraints = []
        for interval in busy_list[d]:
            # Meeting must not overlap: either entirely before or entirely after the busy interval
            constraints.append(Or(s_time + duration <= interval[0], s_time >= interval[1]))
        return And(constraints)
    
    # Add constraints for both participants
    for d in range(3):
        # Nicole's availability
        s.add(Implies(day == d, no_overlap(nicole_busy, d, start)))
        # Ruth's availability
        s.add(Implies(day == d, no_overlap(ruth_busy, d, start)))
    
    # Check for a solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Convert start time to HH:MM format
        hours = 9 + start_val // 60
        minutes = start_val % 60
        end_time = start_val + duration
        end_hours = 9 + end_time // 60
        end_minutes = end_time % 60
        
        # Map day value to day name
        days = ["Monday", "Tuesday", "Wednesday"]
        day_name = days[d_val]
        
        # Format time strings
        start_str = f"{hours:02d}:{minutes:02d}"
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print(f"{day_name}:{start_str}:{end_str}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()