from z3 import *

def schedule_meeting():
    # Define variables
    day = Int('day')
    start_time = Int('start_time')
    
    # James' meetings: (day, start, end) in minutes since 9:00
    james_meetings = [
        (0, 0, 30), (0, 90, 120), (0, 210, 240), (0, 330, 390), (0, 450, 480),
        (1, 0, 120), (1, 150, 180), (1, 210, 390), (1, 420, 480),
        (2, 60, 120), (2, 180, 240), (2, 270, 420),
        (3, 30, 150), (3, 180, 210), (3, 240, 270), (3, 300, 330), (3, 450, 480)
    ]
    
    # Create solver and add constraints
    solver = Optimize()
    solver.add(day >= 0, day <= 3)
    solver.add(start_time >= 0, start_time + 30 <= 480)
    
    # Add constraints for James' meetings
    for m_day, m_start, m_end in james_meetings:
        solver.add(If(day == m_day, Or(start_time >= m_end, start_time + 30 <= m_start), True))
    
    # Set optimization objectives: minimize day first, then start_time
    solver.minimize(day)
    solver.minimize(start_time)
    
    if solver.check() == sat:
        model = solver.model()
        d = model[day].as_long()
        st = model[start_time].as_long()
        day_str = ['Monday', 'Tuesday', 'Wednesday', 'Thursday'][d]
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