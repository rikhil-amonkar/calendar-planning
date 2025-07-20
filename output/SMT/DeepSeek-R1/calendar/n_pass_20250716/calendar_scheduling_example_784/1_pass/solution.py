from z3 import *

def main():
    # Convert time to minutes from 9:00
    # Busy intervals for each participant per day (day0: Monday, day1: Tuesday, day2: Wednesday)
    busy = {
        "Judith": {
            0: [(180, 210)],  # Monday: 12:00-12:30
            2: [(150, 180)]   # Wednesday: 11:30-12:00
        },
        "Timothy": {
            0: [(30, 60), (90, 150), (210, 300), (390, 480)],  # Monday
            1: [(30, 240), (270, 300), (330, 480)],             # Tuesday
            2: [(0, 30), (90, 120), (270, 330), (360, 390), (420, 450)]  # Wednesday
        }
    }
    
    # Create Z3 variables
    day = Int('day')
    start = Int('start')
    end = start + 60  # Meeting duration is 60 minutes
    
    # Hard constraints: day must be 0, 1, or 2; start time must be within work hours
    hard_constraints = [
        day >= 0, day <= 2,
        start >= 0, start <= 420  # 420 = 480 - 60 (ensures end <= 480)
    ]
    
    # For each day, add constraints to avoid busy intervals
    for d in range(3):
        for participant in ["Judith", "Timothy"]:
            if d in busy[participant]:
                for (s_busy, e_busy) in busy[participant][d]:
                    # If meeting is on day `d`, it must not overlap with the busy interval
                    hard_constraints.append(Implies(day == d, Or(end <= s_busy, start >= e_busy)))
    
    # Define strategies for preferences
    strategies = [
        [day != 0, Implies(day == 2, start >= 180)],  # Avoid Monday; on Wednesday, avoid before 12:00
        [day != 0],                                    # Avoid Monday
        []                                              # No additional constraints
    ]
    
    solver = Solver()
    model = None
    
    for strategy_constraints in strategies:
        solver.push()
        solver.add(hard_constraints)
        solver.add(strategy_constraints)
        if solver.check() == sat:
            model = solver.model()
            solver.pop()
            break
        solver.pop()
    
    if model is None:
        print("No solution found, but the problem states there should be one.")
        return
    
    # Extract solution
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    
    # Convert start time to HH:MM format
    hours = 9 + start_val // 60
    minutes = start_val % 60
    start_time = f"{hours:02d}:{minutes:02d}"
    
    # Calculate end time
    end_time_val = start_val + 60
    end_hours = 9 + end_time_val // 60
    end_minutes = end_time_val % 60
    end_time = f"{end_hours:02d}:{end_minutes:02d}"
    
    # Map day value to day name
    days = ["Monday", "Tuesday", "Wednesday"]
    day_name = days[day_val]
    
    print(f"Day: {day_name}, Start: {start_time}, End: {end_time}")

if __name__ == "__main__":
    main()