from z3 import *

def main():
    solver = Solver()

    start = Int('start')
    solver.add(start >= 9*60)  # 540
    solver.add(start <= 17*60 - 30)  # 990

    # Patrick's busy times
    busy_p = [(9*60, 9*60 +30), (10*60, 10*60+30), (13*60+30, 13*60+30 +30), (16*60, 16*60+30)]
    for s, e in busy_p:
        solver.add(Or(start >= e, start + 30 <= s))

    # Kayla's busy times
    busy_k = [(12*60+30, 13*60+30), (15*60, 15*60+30), (16*60, 16*60+30)]
    for s, e in busy_k:
        solver.add(Or(start >= e, start + 30 <= s))

    # Carl's busy times
    busy_c = [(10*60+30, 11*60), (12*60, 12*60+30), (13*60, 13*60+30), (14*60+30, 17*60)]
    for s, e in busy_c:
        solver.add(Or(start >= e, start + 30 <= s))

    # Christian's busy times
    busy_ch = [(9*60, 12*60+30), (13*60, 14*60), (14*60+30, 17*60)]
    for s, e in busy_ch:
        solver.add(Or(start >= e, start + 30 <= s))

    if solver.check() == sat:
        m = solver.model()
        start_val = m.evaluate(start).as_long()
        day = "Monday"
        start_time = start_val
        end_time = start_val + 30

        def format_time(minutes):
            h = minutes // 60
            m = minutes % 60
            return f"{h:02d}:{m:02d}"

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {format_time(start_time)}")
        print(f"End Time: {format_time(end_time)}")
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()