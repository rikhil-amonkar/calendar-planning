from z3 import *

def schedule_meeting():
    s = Solver()

    is_monday = Bool('is_monday')
    start_time = Int('start_time')

    # Time constraints: 9:00 (540) to 16:30 (990)
    s.add(And(start_time >= 540, start_time <= 990))

    # Shirley's busy times
    shirley_monday = [(630, 660), (720, 750), (960, 990)]
    shirley_tuesday = [(570, 600)]

    # Albert's busy times
    albert_monday = [(540, 1020)]
    albert_tuesday = [(570, 600), (690, 750), (780, 960), (990, 1020)]

    # Shirley's constraints
    shirley_mon = And([Or(start_time + 30 <= s, start_time >= e) for (s, e) in shirley_monday])
    shirley_tue = And([Or(start_time + 30 <= s, start_time >= e) for (s, e) in shirley_tuesday])
    shirley_constraints = And(Implies(is_monday, shirley_mon), Implies(Not(is_monday), shirley_tue))
    s.add(shirley_constraints)

    # Albert's constraints
    albert_mon = And([Or(start_time + 30 <= s, start_time >= e) for (s, e) in albert_monday])
    albert_tue = And([Or(start_time + 30 <= s, start_time >= e) for (s, e) in albert_tuesday])
    albert_constraints = And(Implies(is_monday, albert_mon), Implies(Not(is_monday), albert_tue))
    s.add(albert_constraints)

    # Preference constraint: if Tuesday, start_time <= 10:30 (630)
    s.add(If(Not(is_monday), start_time <= 630, True))

    if s.check() == sat:
        m = s.model()
        is_mon = m.evaluate(is_monday)
        st = m.evaluate(start_time).as_long()
        et = st + 30

        day = "Monday" if is_mon else "Tuesday"

        def to_time(mins):
            hours = mins // 60
            mins_remaining = mins % 60
            return f"{hours:02d}:{mins_remaining:02d}"

        print("SOLUTION:")
        print(f"Day: {day}")
        print(f"Start Time: {to_time(st)}")
        print(f"End Time: {to_time(et)}")
    else:
        print("No solution found.")

schedule_meeting()