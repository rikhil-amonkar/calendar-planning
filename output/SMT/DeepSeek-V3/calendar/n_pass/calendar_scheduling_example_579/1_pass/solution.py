from z3 import *

def solve_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the day and work hours
    work_start = 9 * 60  # 9:00 in minutes
    work_end = 17 * 60    # 17:00 in minutes
    meeting_duration = 30  # minutes
    
    # Christine's busy times in minutes since 9:00
    christine_busy = [
        (11 * 60, 11 * 60 + 30),    # 11:00-11:30
        (15 * 60, 15 * 60 + 30)      # 15:00-15:30
    ]
    
    # Helen's busy times in minutes since 9:00
    helen_busy = [
        (9 * 60 + 30, 10 * 60 + 30),  # 9:30-10:30
        (11 * 60, 11 * 60 + 30),       # 11:00-11:30
        (12 * 60, 12 * 60 + 30),       # 12:00-12:30
        (13 * 60 + 30, 16 * 60),       # 13:30-16:00
        (16 * 60 + 30, 17 * 60)        # 16:30-17:00
    ]
    
    # Additional constraint: Helen cannot meet after 15:00
    helen_no_meet_after = 15 * 60  # 15:00
    
    # Possible start times in 30-minute increments within work hours
    possible_starts = range(work_start, work_end - meeting_duration + 1, 30)
    
    # Create a boolean variable for each possible start time
    start_vars = [Bool(f"start_{time}") for time in possible_starts]
    
    # Add constraints: selected start time must not overlap with busy times for both participants
    # and must end before Helen's no-meet-after time
    for i, start in enumerate(possible_starts):
        end = start + meeting_duration
        # Check if this slot is free for Christine
        christine_free = True
        for (busy_start, busy_end) in christine_busy:
            if not (end <= busy_start or start >= busy_end):
                christine_free = False
                break
        # Check if this slot is free for Helen
        helen_free = True
        for (busy_start, busy_end) in helen_busy:
            if not (end <= busy_start or start >= busy_end):
                helen_free = False
                break
        # Additional constraint: meeting must end by 15:00 for Helen
        if end > helen_no_meet_after:
            helen_free = False
        
        # The slot can be selected only if both are free
        s.add(Implies(start_vars[i], And(christine_free, helen_free)))
    
    # Exactly one start time must be selected
    s.add(Or(start_vars))
    for i in range(len(start_vars)):
        for j in range(i + 1, len(start_vars)):
            s.add(Not(And(start_vars[i], start_vars[j])))
    
    # Check for a solution
    if s.check() == sat:
        model = s.model()
        for i, var in enumerate(start_vars):
            if model.evaluate(var):
                start_time = possible_starts[i]
                end_time = start_time + meeting_duration
                # Convert minutes back to HH:MM format
                start_hh = start_time // 60
                start_mm = start_time % 60
                end_hh = end_time // 60
                end_mm = end_time % 60
                print("SOLUTION:")
                print(f"Day: Monday")
                print(f"Start Time: {start_hh:02d}:{start_mm:02d}")
                print(f"End Time: {end_hh:02d}:{end_mm:02d}")
                return
    else:
        print("No solution found")

solve_scheduling()