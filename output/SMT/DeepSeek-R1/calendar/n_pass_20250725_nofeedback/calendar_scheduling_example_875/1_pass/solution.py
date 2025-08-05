from z3 import *

def time_to_minutes(time_str):
    h, m = time_str.split(':')
    h = int(h)
    m = int(m)
    return (h - 9) * 60 + m

def minutes_to_time(minutes):
    total_minutes = minutes
    h = 9 + total_minutes // 60
    m = total_minutes % 60
    return f"{h:02d}:{m:02d}"

natalie_busy = {
    'Monday': [('9:00','9:30'), ('10:00','12:00'), ('12:30','13:00'), ('14:00','14:30'), ('15:00','16:30')],
    'Tuesday': [('9:00','9:30'), ('10:00','10:30'), ('12:30','14:00'), ('16:00','17:00')],
    'Wednesday': [('11:00','11:30'), ('16:00','16:30')],
    'Thursday': [('10:00','11:00'), ('11:30','15:00'), ('15:30','16:00'), ('16:30','17:00')]
}

william_busy = {
    'Monday': [('9:30','11:00'), ('11:30','17:00')],
    'Tuesday': [('9:00','13:00'), ('13:30','16:00')],
    'Wednesday': [('9:00','12:30'), ('13:00','14:30'), ('15:30','16:00'), ('16:30','17:00')],
    'Thursday': [('9:00','10:30'), ('11:00','11:30'), ('12:00','12:30'), ('13:00','14:00'), ('15:00','17:00')]
}

days = ['Monday', 'Tuesday', 'Wednesday', 'Thursday']
solution_found = False
result_day = None
start_time_str = None
end_time_str = None

for day in days:
    s = Int('start')
    solver = Solver()
    solver.add(s >= 0)
    solver.add(s <= 420)
    
    for interval in natalie_busy[day]:
        start_busy = time_to_minutes(interval[0])
        end_busy = time_to_minutes(interval[1])
        solver.add(Or(s + 60 <= start_busy, s >= end_busy))
    
    for interval in william_busy[day]:
        start_busy = time_to_minutes(interval[0])
        end_busy = time_to_minutes(interval[1])
        solver.add(Or(s + 60 <= start_busy, s >= end_busy))
    
    if solver.check() == sat:
        model = solver.model()
        start_val = model[s].as_long()
        end_val = start_val + 60
        start_time_str = minutes_to_time(start_val)
        end_time_str = minutes_to_time(end_val)
        result_day = day
        solution_found = True
        break

if solution_found:
    print("SOLUTION:")
    print(f"Day: {result_day}")
    print(f"Start Time: {start_time_str}")
    print(f"End Time: {end_time_str}")
else:
    print("No solution found, but the problem states there is one.")