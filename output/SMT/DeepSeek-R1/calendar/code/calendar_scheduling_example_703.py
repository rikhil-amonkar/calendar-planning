from z3 import *

def schedule_meeting():
    # Define variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Participants' meetings: (day, start, end) in minutes since 9:00
    stephanie_meetings = [
        (0, 30, 60), (0, 90, 120), (0, 150, 180), (0, 300, 330),
        (1, 180, 240),
        (2, 0, 60), (2, 240, 300)
    ]
    betty_meetings = [
        (0, 0, 60), (0, 120, 150), (0, 330, 360), (0, 390, 420),
        (1, 0, 30), (1, 150, 180), (1, 210, 330), (1, 390, 420),
        (2, 60, 150), (2, 180, 300), (2, 330, 480)
    ]
    
    # Create solver and add basic constraints
    solver = Solver()
    solver.add(day >= 0, day <= 2)
    solver.add(start_time >= 0, start_time + 60 <= 480)
    
    # Betty's Tuesday after 12:30 constraint (12:30 is 210 minutes from 9:00)
    solver.add(Implies(day == 1, start_time + 60 <= 210))
    
    # Add constraints for avoiding meeting overlaps
    def add_conflicts(meetings):
        for m_day, m_start, m_end in meetings:
            solver.add(If(day == m_day, Or(start_time >= m_end, start_time + 60 <= m_start), True))
    
    add_conflicts(stephanie_meetings)
    add_conflicts(betty_meetings)
    
    # Check with Stephanie's preference (day != 0) first
    preferred = Solver()
    preferred.add(solver.assertions())
    preferred.add(day != 0)
    
    if preferred.check() == sat:
        model = preferred.model()
    else:
        solver.check()
        model = solver.model()
    
    # Extract solution
    d = model[day].as_long()
    st = model[start_time].as_long()
    day_str = ['Monday', 'Tuesday', 'Wednesday'][d]
    start = f"{9 + st // 60:02}:{st % 60:02}"
    end = f"{9 + (st + 60) // 60:02}:{(st + 60) % 60:02}"
    return (day_str, start, end)

result = schedule_meeting()
print(f"Day: {result[0]}")
print(f"Start Time: {result[1]}")
print(f"End Time: {result[2]}")