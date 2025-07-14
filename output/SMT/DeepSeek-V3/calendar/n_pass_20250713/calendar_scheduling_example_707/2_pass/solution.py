from z3 import *

def solve_scheduling():
    # Create the solver
    s = Solver()

    # Define the variables
    day = Int('day')  # 0: Monday, 1: Tuesday, 2: Wednesday
    start_time = Int('start_time')  # in minutes from 9:00 (e.g., 9:30 is 30)
    end_time = Int('end_time')

    # Possible days: Monday (0), Tuesday (1), Wednesday (2)
    s.add(Or(day == 0, day == 1, day == 2))
    
    # Ryan cannot meet on Wednesday (day 2)
    s.add(day != 2)
    
    # Meeting duration is exactly 30 minutes
    s.add(end_time == start_time + 30)
    
    # Meeting must be within work hours (9:00 to 17:00, so 0 to 480 minutes from 9:00)
    s.add(start_time >= 0)
    s.add(end_time <= 480)  # 17:00 is 8 hours after 9:00 (8*60=480)
    
    # Ryan's busy slots (converted to minutes from 9:00)
    ryan_busy = {
        0: [(30, 60), (120, 180), (240, 270), (390, 420)],  # Monday
        1: [(150, 210), (390, 420)],  # Tuesday
        2: [(180, 240), (390, 420), (450, 480)]  # Wednesday (but excluded)
    }
    
    # Adam's busy slots (converted to minutes from 9:00)
    adam_busy = {
        0: [(0, 90), (120, 270), (300, 420), (450, 480)],  # Monday
        1: [(0, 60), (90, 390), (420, 480)],  # Tuesday
        2: [(0, 30), (60, 120), (150, 330), (360, 390), (420, 450)]  # Wednesday
    }
    
    # Adam prefers to avoid Monday before 14:30 (14:30 is 5.5 hours after 9:00, 5.5*60=330 minutes)
    # So if day is Monday, start_time should be >= 330 (14:30)
    s.add(Implies(day == 0, start_time >= 330))
    
    # Function to add no-overlap constraints
    def add_no_overlap_constraints(busy_slots, day_var, start, end):
        for d in busy_slots:
            slots = busy_slots[d]
            for slot in slots:
                s.add(Not(And(day_var == d,
                              Not(Or(end <= slot[0], start >= slot[1])))))
    
    # Add constraints for Ryan and Adam
    add_no_overlap_constraints(ryan_busy, day, start_time, end_time)
    add_no_overlap_constraints(adam_busy, day, start_time, end_time)
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        day_val = model[day].as_long()
        start_val = model[start_time].as_long()
        end_val = model[end_time].as_long()
        
        # Convert day to string
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Convert start and end times to HH:MM format
        start_hh = 9 + start_val // 60
        start_mm = start_val % 60
        end_hh = 9 + end_val // 60
        end_mm = end_val % 60
        
        # Format as two-digit strings
        start_time_str = f"{start_hh:02d}:{start_mm:02d}"
        end_time_str = f"{end_hh:02d}:{end_mm:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {day_str}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()