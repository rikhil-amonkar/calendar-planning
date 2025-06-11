from z3 import *

def main():
    start = Int('start')
    solver = Solver()
    
    busy_intervals = [
        (60, 90), (420, 450),    # Emily
        (90, 120), (300, 330),    # Maria
        (30, 60), (90, 210), (270, 300), (330, 390), (420, 480),  # Carl
        (30, 120), (150, 180), (210, 270), (300, 360), (420, 480),  # David
        (30, 90), (120, 150), (210, 270), (330, 480)   # Frank
    ]
    
    solver.add(start >= 0)
    solver.add(start <= 450)
    
    for (b_start, b_end) in busy_intervals:
        solver.add(Or(start + 30 <= b_start, start >= b_end))
    
    if solver.check() == sat:
        model = solver.model()
        start_minutes = model[start].as_long()
        
        total_minutes = start_minutes
        hours = total_minutes // 60
        minutes = total_minutes % 60
        start_hour = 9 + hours
        start_minute = minutes
        start_str = f"{start_hour}:{start_minute:02d}"
        
        end_minutes = total_minutes + 30
        hours_end = end_minutes // 60
        minutes_end = end_minutes % 60
        end_hour = 9 + hours_end
        end_minute = minutes_end
        end_str = f"{end_hour}:{end_minute:02d}"
        
        print("Monday")
        print(start_str)
        print(end_str)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()