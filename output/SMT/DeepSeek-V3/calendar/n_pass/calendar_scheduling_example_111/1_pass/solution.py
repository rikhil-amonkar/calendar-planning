from z3 import *

def solve_scheduling():
    # Initialize the solver
    solver = Solver()
    
    # Define the start time in minutes from 9:00 (0 minutes is 9:00)
    start_time = Int('start_time')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total working hours: 9:00 to 17:00 is 8 hours = 480 minutes
    max_time = 480  # 17:00 is 480 minutes from 9:00 (since 17:00 - 9:00 = 8 hours)
    
    # Constraint: start_time must be >= 0 and <= (max_time - duration)
    solver.add(start_time >= 0)
    solver.add(start_time <= max_time - duration)
    
    # Define each person's busy slots in minutes from 9:00
    # Gregory's busy slots: 9:00-10:00 (0-60), 10:30-11:30 (90-150), 12:30-13:00 (210-240), 13:30-14:00 (270-300)
    gregory_busy = [(0, 60), (90, 150), (210, 240), (270, 300)]
    
    # Natalie is free all day
    natalie_busy = []
    
    # Christine's busy slots: 9:00-11:30 (0-150), 13:30-17:00 (270-480)
    christine_busy = [(0, 150), (270, 480)]
    
    # Vincent's busy slots: 9:00-9:30 (0-30), 10:30-12:00 (90-180), 12:30-14:00 (210-300), 14:30-17:00 (330-480)
    vincent_busy = [(0, 30), (90, 180), (210, 300), (330, 480)]
    
    # Function to add constraints that the meeting does not overlap with any busy slot
    def add_no_overlap_constraints(busy_slots):
        for (busy_start, busy_end) in busy_slots:
            # The meeting should not overlap with this busy slot: either meeting ends before busy starts or starts after busy ends
            solver.add(Or(
                start_time + duration <= busy_start,
                start_time >= busy_end
            ))
    
    # Add constraints for each participant
    add_no_overlap_constraints(gregory_busy)
    add_no_overlap_constraints(natalie_busy)  # no constraints actually added here
    add_no_overlap_constraints(christine_busy)
    add_no_overlap_constraints(vincent_busy)
    
    # Check for a solution
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start_time].as_long()
        
        # Calculate start and end times in HH:MM format
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + duration
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_hour:02d}:{start_minute:02d}")
        print(f"End Time: {end_hour:02d}:{end_minute:02d}")
    else:
        print("No solution found")

solve_scheduling()