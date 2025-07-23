from z3 import *

def main():
    s = Optimize()
    
    # Define persons and their available time slots by day index
    persons = {
        'A': {0: (8*60, 12*60),  2: (10*60, 15*60)},   # Monday (0), Wednesday (2)
        'B': {1: (9*60, 11*60),  3: (14*60, 16*60)},   # Tuesday (1), Thursday (3)
        'C': {0: (13*60, 17*60), 4: (8*60, 10*60)},     # Monday (0), Friday (4)
        'D': {1: (13*60, 15*60), 2: (8*60, 12*60)},     # Tuesday (1), Wednesday (2)
        'E': {2: (14*60, 17*60), 4: (13*60, 17*60)}     # Wednesday (2), Friday (4)
    }
    day_names = ['Monday', 'Tuesday', 'Wednesday', 'Thursday', 'Friday']

    # Assignment variables for each person
    assignment = {p: Int(f'x_{p}') for p in persons}
    
    # Each person assigned to one of their available days
    for p, days in persons.items():
        s.add(Or([assignment[p] == d for d in days.keys()]))
    
    # Meeting start/end times for each day
    starts = [Int(f'start_{d}') for d in range(5)]
    ends = [Int(f'end_{d}') for d in range(5)]
    
    # Basic meeting constraints
    for d in range(5):
        s.add(starts[d] >= 8*60, ends[d] <= 17*60, ends[d] - starts[d] >= 60)
    
    # Ensure meetings fit all assigned participants' availability
    for p, days in persons.items():
        for d, (low, high) in days.items():
            s.add(Implies(assignment[p] == d, 
                          And(starts[d] >= low, ends[d] <= high)))
    
    # Maximize total meeting time
    total_time = Sum([ends[d] - starts[d] for d in range(5)])
    s.maximize(total_time)
    
    # Solve and output results
    if s.check() == sat:
        m = s.model()
        print("Person assignments:")
        for p in persons:
            day_idx = m[assignment[p]].as_long()
            print(f"- Person {p}: {day_names[day_idx]}")
        
        print("\nMeeting schedule:")
        for d in range(5):
            start_val = m[starts[d]].as_long()
            end_val = m[ends[d]].as_long()
            print(f"{day_names[d]}: "
                  f"{start_val//60:02d}:{start_val%60:02d} to "
                  f"{end_val//60:02d}:{end_val%60:02d} "
                  f"({(end_val - start_val)//60}h{(end_val - start_val)%60}m)")
        print(f"\nTotal meeting time: {m.evaluate(total_time).as_long()//60}h"
              f"{m.evaluate(total_time).as_long()%60}m")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()