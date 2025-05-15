from z3 import *

def schedule_meeting():
    # Define variables
    day = Int('day')
    start_time = Int('start_time')
    
    # Samuel's meetings: (day, start, end) in minutes since 9:00
    samuel_meetings = [
        (0, 90, 120), (0, 180, 210), (0, 240, 360), (0, 390, 420),
        (1, 0, 120), (1, 150, 180), (1, 210, 390), (1, 420, 480),
        (2, 90, 120), (2, 150, 180), (2, 210, 240), (2, 300, 330), (2, 360, 420)
    ]
    
    # Create solver with optimization
    solver = Optimize()
    solver.add(day >= 0, day <= 2)  # Monday(0), Tuesday(1), Wednesday(2)
    solver.add(start_time >= 0, start_time + 30 <= 480)  # 30-minute meeting within 9:00-17:00
    
    # Add Samuel's meeting constraints
    for m_day, m_start, m_end in samuel_meetings:
        solver.add(If(day == m_day, Or(start_time >= m_end, start_time + 30 <= m_start), True))
    
    # Set optimization objectives: prioritize earliest day then earliest time
    solver.minimize(day)
    solver.minimize(start_time)
    
    if solver.check() == sat:
        model = solver.model()
        d = model[day].as_long()
        st = model[start_time].as_long()
        day_str = ['Monday', 'Tuesday', 'Wednesday'][d]
        start_h = 9 + st // 60
        start_m = st % 60
        end_time = st + 30
        end_h = 9 + end_time // 60
        end_m = end_time % 60
        start = f"{start_h:02}:{start_m:02}"
        end = f"{end_h:02}:{end_m:02}"
        return (day_str, start, end)
    else:
        return ("No solution found", "", "")

result = schedule_meeting()
print(f"Day: {result[0]}")
print(f"Start Time: {result[1]}")
print(f"End Time: {result[2]}")