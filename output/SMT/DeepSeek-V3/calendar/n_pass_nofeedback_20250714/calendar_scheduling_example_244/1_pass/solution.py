from z3 import *

def solve_scheduling():
    # Create solver instance
    s = Solver()
    
    # Define variables for start time (in minutes from 9:00)
    start_h = Int('start_h')
    start_m = Int('start_m')
    
    # Meeting duration is 30 minutes
    duration = 30
    
    # Total work hours: 9:00 to 17:00 (8 hours = 480 minutes)
    total_minutes_in_day = (17 - 9) * 60  # 480 minutes (from 9:00 to 17:00)
    
    # Constraints for start_h and start_m to be within work hours
    s.add(start_h >= 9)
    s.add(start_h < 17)
    s.add(start_m >= 0)
    s.add(start_m < 60)
    
    # Calculate start time in total minutes from 0:00 for easier comparison
    start_total = start_h * 60 + start_m
    end_total = start_total + duration
    
    # Constraint: meeting must end by 17:00
    s.add(end_total <= 17 * 60)
    
    # Constraint: meeting must start at or after 9:00
    s.add(start_total >= 9 * 60)
    
    # Now, add constraints for each person's busy times
    
    # Walter has no meetings, so no constraints
    
    # Cynthia's busy times (in minutes from 0:00):
    # 9:00-9:30, 10:00-10:30, 13:30-14:30, 15:00-16:00
    cynthia_busy = [
        (9*60, 9*60 + 30),
        (10*60, 10*60 + 30),
        (13*60 + 30, 14*60 + 30),
        (15*60, 16*60)
    ]
    for (busy_start, busy_end) in cynthia_busy:
        # The meeting must not overlap with this busy interval
        s.add(Or(
            end_total <= busy_start,
            start_total >= busy_end
        ))
    
    # Ann's busy times:
    # 10:00-11:00, 13:00-13:30, 14:00-15:00, 16:00-16:30
    ann_busy = [
        (10*60, 11*60),
        (13*60, 13*60 + 30),
        (14*60, 15*60),
        (16*60, 16*60 + 30)
    ]
    for (busy_start, busy_end) in ann_busy:
        s.add(Or(
            end_total <= busy_start,
            start_total >= busy_end
        ))
    
    # Catherine's busy times:
    # 9:00-11:30, 12:30-13:30, 14:30-17:00
    catherine_busy = [
        (9*60, 11*60 + 30),
        (12*60 + 30, 13*60 + 30),
        (14*60 + 30, 17*60)
    ]
    for (busy_start, busy_end) in catherine_busy:
        s.add(Or(
            end_total <= busy_start,
            start_total >= busy_end
        ))
    
    # Kyle's busy times:
    # 9:00-9:30, 10:00-11:30, 12:00-12:30, 13:00-14:30, 15:00-16:00
    kyle_busy = [
        (9*60, 9*60 + 30),
        (10*60, 11*60 + 30),
        (12*60, 12*60 + 30),
        (13*60, 14*60 + 30),
        (15*60, 16*60)
    ]
    for (busy_start, busy_end) in kyle_busy:
        s.add(Or(
            end_total <= busy_start,
            start_total >= busy_end
        ))
    
    # Check if a solution exists
    if s.check() == sat:
        m = s.model()
        start_h_val = m.eval(start_h).as_long()
        start_m_val = m.eval(start_m).as_long()
        
        # Calculate end time
        end_total_val = start_h_val * 60 + start_m_val + duration
        end_h_val = end_total_val // 60
        end_m_val = end_total_val % 60
        
        # Format the output
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_h_val:02d}:{start_m_val:02d}")
        print(f"End Time: {end_h_val:02d}:{end_m_val:02d}")
    else:
        print("No solution found")

solve_scheduling()