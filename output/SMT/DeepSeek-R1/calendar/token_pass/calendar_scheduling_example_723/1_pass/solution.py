from z3 import *

def main():
    # Initialize solver
    s = Optimize()
    
    # Define day and start time variables
    day = Int('day')
    start = Int('start')
    
    # Meeting duration in minutes
    duration = 30
    
    # Total minutes in workday (9:00 to 17:00 is 8 hours = 480 minutes)
    total_minutes = 480
    
    # Day constraints: 0 = Monday, 2 = Wednesday (Tuesday excluded per Arthur's constraint)
    s.add(Or(day == 0, day == 2))
    
    # Start time must be within work hours and allow duration
    s.add(start >= 0)
    s.add(start + duration <= total_minutes)
    
    # Arthur's busy intervals (in minutes from 9:00)
    arthur_busy = {
        0: [(120, 150), (270, 300), (360, 390)],  # Monday
        2: [(60, 90), (120, 150), (180, 210), (300, 330), (420, 450)]  # Wednesday
    }
    
    # Michael's busy intervals
    michael_busy = {
        0: [(0, 180), (210, 240), (300, 330), (360, 480)],  # Monday
        2: [(60, 210), (240, 270)]  # Wednesday
    }
    
    # Function to add no-overlap constraints
    def add_no_overlap(busy_intervals, person_start):
        for interval in busy_intervals:
            b_start, b_end = interval
            # Meeting must not overlap with any busy interval
            s.add(Or(person_start >= b_end, person_start + duration <= b_start))
    
    # Add constraints for Arthur and Michael based on selected day
    for d in [0, 2]:
        # If day is d, then add corresponding constraints
        cond = (day == d)
        # Arthur's constraints
        for interval in arthur_busy[d]:
            b_start, b_end = interval
            s.add(Implies(cond, Or(start >= b_end, start + duration <= b_start)))
        # Michael's constraints
        for interval in michael_busy[d]:
            b_start, b_end = interval
            s.add(Implies(cond, Or(start >= b_end, start + duration <= b_start)))
    
    # Minimize day and start time for earliest availability
    s.minimize(day * total_minutes + start)
    
    # Check solution
    if s.check() == sat:
        m = s.model()
        d_val = m[day].as_long()
        start_val = m[start].as_long()
        
        # Convert day value to string
        days = {0: "Monday", 2: "Wednesday"}
        day_str = days[d_val]
        
        # Convert start time to HH:MM format
        start_hour = 9 + start_val // 60
        start_minute = start_val % 60
        end_val = start_val + duration
        end_hour = 9 + end_val // 60
        end_minute = end_val % 60
        
        # Format time strings
        start_time = f"{start_hour:02d}:{start_minute:02d}"
        end_time = f"{end_hour:02d}:{end_minute:02d}"
        
        print(f"{day_str} {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()