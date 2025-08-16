from z3 import *

def main():
    # Define variables
    day = Int('day')
    start = Int('start')
    end = Int('end')
    solver = Solver()

    # Basic constraints
    solver.add(Or(day == 0, day == 1, day == 2))
    solver.add(start >= 9*60, start <= 16*60)  # 9:00 to 16:00 (start)
    solver.add(end == start + 60)  # 1 hour meeting

    # Stephanie's existing meetings (converted to minutes)
    steph_meetings = {
        0: [(9*60+30, 10*60), (10*60+30, 11*60), (11*60+30, 12*60), (14*60, 14*60+30)],
        1: [(12*60, 13*60)],
        2: [(9*60, 10*60), (13*60, 14*60)],
    }

    # Betty's existing meetings
    betty_meetings = {
        0: [(9*60, 10*60), (11*60, 11*60+30), (14*60+30, 15*60), (15*60+30, 16*60)],
        1: [(9*60, 9*60+30), (11*60+30, 12*60), (12*60+30, 14*60+30), (15*60+30, 16*60)],
        2: [(10*60, 11*60+30), (12*60, 14*60), (14*60+30, 17*60)],
    }

    # Add constraints for Stephanie's existing meetings
    for d in steph_meetings:
        for s_i, e_i in steph_meetings[d]:
            # If day == d, then new meeting does not overlap with (s_i, e_i)
            solver.add(Implies(day == d, Or(start >= e_i, end <= s_i)))

    # Add constraints for Betty's existing meetings
    for d in betty_meetings:
        for s_i, e_i in betty_meetings[d]:
            solver.add(Implies(day == d, Or(start >= e_i, end <= s_i)))

    # Betty cannot meet on Tuesday after 12:30 PM (750 minutes)
    solver.add(Implies(day == 1, end <= 12*60 + 30))

    # Try to avoid Monday (Stephanie's preference)
    solver.push()
    solver.add(day != 0)

    if solver.check() == sat:
        model = solver.model()
    else:
        solver.pop()  # Remove the day != 0 constraint
        if solver.check() == sat:
            model = solver.model()
        else:
            print("No solution found")
            return

    # Extract values
    day_val = model[day].as_long()
    start_val = model[start].as_long()
    end_val = model[end].as_long()

    # Convert to day name
    days = ['Monday', 'Tuesday', 'Wednesday']
    day_str = days[day_val]

    # Convert start and end to HH:MM format
    def to_time_str(m):
        h = m // 60
        mi = m % 60
        return f"{h:02d}:{mi:02d}"

    # Output the solution
    print("SOLUTION:")
    print(f"Day: {day_str}")
    print(f"Start Time: {to_time_str(start_val)}")
    print(f"End Time: {to_time_str(end_val)}")

if __name__ == "__main__":
    main()