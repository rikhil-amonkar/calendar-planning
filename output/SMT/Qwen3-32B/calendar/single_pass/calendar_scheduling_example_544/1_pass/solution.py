from z3 import *

def main():
    # Define variables
    S = Int('S')
    solver = Solver()

    # Meeting must be during 9:00-17:00 (540 to 1020) but ends by 11:00 (660)
    solver.add(S >= 9*60)
    solver.add(S + 30 <= 11*60)

    # Albert's blocked intervals (adjusted for his not meeting after 11:00)
    blocked = [(9*60, 10*60), (10*60 + 30, 11*60)]
    for b_start, b_end in blocked:
        solver.add(Or(S + 30 <= b_start, S >= b_end))

    if solver.check() == sat:
        model = solver.model()
        s_val = model[S].as_long()
        start_hours = s_val // 60
        start_mins = s_val % 60
        start_time = f"{start_hours:02d}:{start_mins:02d}"
        end_val = s_val + 30
        end_hours = end_val // 60
        end_mins = end_val % 60
        end_time = f"{end_hours:02d}:{end_mins:02d}"
        print("SOLUTION:")
        print(f"Day: Monday")
        print(f"Start Time: {start_time}")
        print(f"End Time: {end_time}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()