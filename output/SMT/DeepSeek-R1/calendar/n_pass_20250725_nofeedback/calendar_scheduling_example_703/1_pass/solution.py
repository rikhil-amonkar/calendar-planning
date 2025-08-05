from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define variables
    day = Int('day')
    start_minutes = Int('start_minutes')
    
    # Day must be 0 (Monday), 1 (Tuesday), or 2 (Wednesday)
    s.add(day >= 0, day <= 2)
    # Start time must allow the meeting to end by 17:00 (480 minutes from 9:00)
    s.add(start_minutes >= 0, start_minutes <= 420)
    
    # Define existing meetings in minutes from 9:00
    steph_monday = [(30, 60), (90, 120), (150, 180), (300, 330)]
    betty_monday = [(0, 60), (120, 150), (330, 360), (390, 420)]
    
    steph_tuesday = [(180, 240)]
    betty_tuesday = [(0, 30), (150, 180), (210, 330), (390, 420)]
    
    steph_wednesday = [(0, 60), (240, 300)]
    betty_wednesday = [(60, 150), (180, 300), (330, 480)]
    
    # Monday constraints: no overlap with existing meetings
    monday_constraints = []
    for s_busy, e_busy in steph_monday:
        monday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    for s_busy, e_busy in betty_monday:
        monday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    monday_ok = And(monday_constraints)
    
    # Tuesday constraints: no overlap with meetings and meeting ends by 12:30 (210 minutes)
    tuesday_constraints = []
    for s_busy, e_busy in steph_tuesday:
        tuesday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    for s_busy, e_busy in betty_tuesday:
        tuesday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    tuesday_constraints.append(start_minutes + 60 <= 210)
    tuesday_ok = And(tuesday_constraints)
    
    # Wednesday constraints: no overlap with existing meetings
    wednesday_constraints = []
    for s_busy, e_busy in steph_wednesday:
        wednesday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    for s_busy, e_busy in betty_wednesday:
        wednesday_constraints.append(Or(start_minutes + 60 <= s_busy, start_minutes >= e_busy))
    wednesday_ok = And(wednesday_constraints)
    
    # Add day-specific constraints to solver
    s.add(If(day == 0, monday_ok, If(day == 1, tuesday_ok, wednesday_ok)))
    
    # First, try without Monday (Stephanie's preference)
    s.push()
    s.add(day != 0)
    if s.check() == sat:
        m = s.model()
        d = m[day].as_long()
        st = m[start_minutes].as_long()
    else:
        s.pop()
        s.check()
        m = s.model()
        d = m[day].as_long()
        st = m[start_minutes].as_long()
    
    # Convert day to string
    days = ["Monday", "Tuesday", "Wednesday"]
    day_str = days[d]
    
    # Calculate start and end times
    start_hour = 9 + st // 60
    start_min = st % 60
    end_minutes = st + 60
    end_hour = 9 + end_minutes // 60
    end_min = end_minutes % 60
    
    # Format output
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {start_hour:02d}:{start_min:02d}")
    print(f"End Time: {end_hour:02d}:{end_min:02d}")

if __name__ == '__main__':
    main()