from z3 import *

def main():
    d = Int('d')  # Day: 0 = Monday, 1 = Tuesday
    s = Int('s')  # Time slot (0 to 15, each 30 minutes starting from 9:00)
    
    solver = Solver()
    
    # Only Monday (0) and Tuesday (1) are considered
    solver.add(Or(d == 0, d == 1))
    solver.add(s >= 0, s <= 15)  # 16 slots in a day (0 to 15)
    
    # Cheryl's busy slots
    cheryl_busy = {
        0: [0, 5, 6, 7, 13],  # Monday
        1: [12]                # Tuesday
    }
    for day, busy_slots in cheryl_busy.items():
        solver.add(If(d == day, And([s != slot for slot in busy_slots]), True))
    
    # Kyle's constraints
    solver.add(If(d == 0, False, True))  # Monday entirely busy
    solver.add(If(d == 1, s == 0, True)) # Tuesday only free at slot 0
    
    if solver.check() == sat:
        model = solver.model()
        day_val = model[d].as_long()
        slot_val = model[s].as_long()
        
        days = ["Monday", "Tuesday", "Wednesday"]
        day_str = days[day_val]
        
        # Convert slot to start time (in minutes from 9:00)
        start_minutes = slot_val * 30
        start_hour = 9 + start_minutes // 60
        start_minute = start_minutes % 60
        end_minutes = start_minutes + 30
        end_hour = 9 + end_minutes // 60
        end_minute = end_minutes % 60
        
        start_time = f"{start_hour}:{start_minute:02d}"
        end_time = f"{end_hour}:{end_minute:02d}"
        
        print(f"Day: {day_str}")
        print(f"Start time: {start_time}")
        print(f"End time: {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()