from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the possible days (0: Monday, 1: Tuesday, 2: Wednesday)
    day = Int('day')
    s.add(day >= 0, day <= 2)
    
    # Define the start time in minutes from 9:00 (540 minutes in 24-hour format)
    start_time = Int('start_time')
    # Meeting duration is 30 minutes
    duration = 30
    # Work hours are 9:00 to 17:00 (540 to 1020 minutes)
    # The meeting must start no earlier than 9:00 and end by 17:00
    s.add(start_time >= 0, start_time + duration <= 480)  # 540 + 480 = 1020 (17:00)
    
    # Ronald's blocked times per day in minutes from 9:00
    # Format: {day: [(start1, end1), (start2, end2), ...]}
    ronald_blocked = {
        0: [(90, 120), (180, 210), (390, 420)],  # Monday: 10:30-11:00, 12:00-12:30, 15:30-16:00
        1: [(0, 30), (180, 210), (390, 450)],     # Tuesday: 9:00-9:30, 12:00-12:30, 15:30-16:30
        2: [(30, 90), (120, 180), (210, 240), (270, 300), (450, 480)]  # Wednesday: 9:30-10:30, 11:00-12:00, 12:30-13:00, 13:30-14:00, 16:30-17:00
    }
    
    # Amber's blocked times per day in minutes from 9:00
    amber_blocked = {
        0: [(0, 30), (60, 90), (150, 180), (210, 300), (330, 360), (390, 480)],  # Monday: 9:00-9:30, 10:00-10:30, 11:30-12:00, 12:30-14:00, 14:30-15:00, 15:30-17:00
        1: [(0, 30), (60, 150), (180, 210), (270, 450), (450, 480)],  # Tuesday: 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:30-15:30, 16:30-17:00
        2: [(0, 30), (60, 90), (120, 270), (360, 390)]  # Wednesday: 9:00-9:30, 10:00-10:30, 11:00-13:30, 15:00-15:30
    }
    
    # Constraints for Ronald's availability
    def add_blocked_constraints(blocked_times, day_var, time_var):
        constraints = []
        for d in blocked_times:
            for (start, end) in blocked_times[d]:
                # If the current day is d, then the meeting must not overlap with any blocked interval
                constraints.append(Implies(day_var == d, Not(And(time_var < end, time_var + duration > start))))
        return And(constraints)
    
    s.add(add_blocked_constraints(ronald_blocked, day, start_time))
    s.add(add_blocked_constraints(amber_blocked, day, start_time))
    
    # To find the earliest time, we minimize the start_time
    # We'll use the optimizer instead of the solver to find the minimal start_time
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(start_time + day * 480)  # Prioritize earlier days, then earlier times
    
    # Check for a solution
    if opt.check() == sat:
        m = opt.model()
        day_val = m[day].as_long()
        start_val = m[start_time].as_long()
        
        # Convert day_val to day name
        days = ['Monday', 'Tuesday', 'Wednesday']
        selected_day = days[day_val]
        
        # Calculate start and end times in HH:MM format
        total_minutes = 540 + start_val  # 9:00 is 540 minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_time_str = f"{hours:02d}:{minutes:02d}"
        
        end_time_val = total_minutes + duration
        end_hours = end_time_val // 60
        end_minutes = end_time_val % 60
        end_time_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        # Print the solution
        print("SOLUTION:")
        print(f"Day: {selected_day}")
        print(f"Start Time: {start_time_str}")
        print(f"End Time: {end_time_str}")
    else:
        print("No solution found")

solve_scheduling()