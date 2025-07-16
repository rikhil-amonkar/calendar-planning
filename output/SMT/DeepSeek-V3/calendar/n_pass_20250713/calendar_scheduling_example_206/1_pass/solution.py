from z3 import *

def solve_meeting_scheduling():
    # Initialize the solver
    s = Solver()
    
    # Define the start time in minutes from 00:00 (but constrained within 9:00-17:00)
    start_time = Int('start_time')
    
    # Work hours are 9:00 (540) to 17:00 (1020)
    # Meeting duration is 30 minutes
    s.add(start_time >= 540)  # 9:00
    s.add(start_time + 30 <= 1020)  # Ends by 17:00
    
    # Margaret's preference: not before 14:30 (870)
    s.add(start_time >= 870)
    
    # Define each participant's busy slots in minutes from 00:00
    # Shirley's busy slots: 10:30-11:00 (630-660), 12:00-12:30 (720-750)
    s.add(Not(And(start_time < 660, start_time + 30 > 630)))  # overlaps with 10:30-11:00
    s.add(Not(And(start_time < 750, start_time + 30 > 720)))  # overlaps with 12:00-12:30
    
    # Jacob's busy slots: 9:00-9:30 (540-570), 10:00-10:30 (600-630), 11:00-11:30 (660-690), 12:30-13:30 (750-810), 14:30-15:00 (870-900)
    s.add(Not(And(start_time < 570, start_time + 30 > 540)))
    s.add(Not(And(start_time < 630, start_time + 30 > 600)))
    s.add(Not(And(start_time < 690, start_time + 30 > 660)))
    s.add(Not(And(start_time < 810, start_time + 30 > 750)))
    s.add(Not(And(start_time < 900, start_time + 30 > 870)))
    
    # Stephen's busy slots: 11:30-12:00 (690-720), 12:30-13:00 (750-780)
    s.add(Not(And(start_time < 720, start_time + 30 > 690)))
    s.add(Not(And(start_time < 780, start_time + 30 > 750)))
    
    # Margaret's busy slots: 9:00-9:30 (540-570), 10:30-12:30 (630-750), 13:00-13:30 (780-810), 15:00-15:30 (900-930), 16:30-17:00 (990-1020)
    s.add(Not(And(start_time < 570, start_time + 30 > 540)))
    s.add(Not(And(start_time < 750, start_time + 30 > 630)))
    s.add(Not(And(start_time < 810, start_time + 30 > 780)))
    s.add(Not(And(start_time < 930, start_time + 30 > 900)))
    s.add(Not(And(start_time < 1020, start_time + 30 > 990)))
    
    # Mason's busy slots: 9:00-10:00 (540-600), 10:30-11:00 (630-660), 11:30-12:30 (690-750), 13:00-13:30 (780-810), 14:00-14:30 (840-870), 16:30-17:00 (990-1020)
    s.add(Not(And(start_time < 600, start_time + 30 > 540)))
    s.add(Not(And(start_time < 660, start_time + 30 > 630)))
    s.add(Not(And(start_time < 750, start_time + 30 > 690)))
    s.add(Not(And(start_time < 810, start_time + 30 > 780)))
    s.add(Not(And(start_time < 870, start_time + 30 > 840)))
    s.add(Not(And(start_time < 1020, start_time + 30 > 990)))
    
    # Check if there's a solution
    if s.check() == sat:
        m = s.model()
        start_min = m[start_time].as_long()
        
        # Convert minutes back to HH:MM format
        hours = start_min // 60
        minutes = start_min % 60
        start_str = f"{hours:02d}:{minutes:02d}"
        
        end_min = start_min + 30
        end_hours = end_min // 60
        end_minutes = end_min % 60
        end_str = f"{end_hours:02d}:{end_minutes:02d}"
        
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_str}")
        print(f"End Time: {end_str}")
    else:
        print("No solution found")

solve_meeting_scheduling()