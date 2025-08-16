from z3 import *

def schedule_meeting():
    opt = Optimize()

    day = Int('day')
    start_time = Int('start_time')

    # Constraints on day and start_time
    opt.add(day >= 0, day <= 2)
    opt.add(start_time >= 540, start_time <= 990)  # 9:00 to 16:30 in minutes since midnight

    # Define the meetings for each day
    meetings_mon = [(630, 660), (720, 750), (780, 900), (930, 990)]
    meetings_tue = [(540, 720), (840, 930), (990, 1020)]
    meetings_wed = [(630, 660), (690, 720), (750, 780), (840, 870), (900, 960)]

    # Add constraints for Monday
    for s, e in meetings_mon:
        opt.add(Implies(day == 0, Or(start_time + 30 <= s, start_time >= e)))

    # Add constraints for Tuesday
    for s, e in meetings_tue:
        opt.add(Implies(day == 1, Or(start_time + 30 <= s, start_time >= e)))

    # Add constraints for Wednesday
    for s, e in meetings_wed:
        opt.add(Implies(day == 2, Or(start_time + 30 <= s, start_time >= e)))

    # Optimization goals
    opt.minimize(day)
    opt.minimize(start_time)

    if opt.check() == sat:
        m = opt.model()
        d = m.eval(day).as_long()
        st = m.eval(start_time).as_long()
        et = st + 30

        days = ['Monday', 'Tuesday', 'Wednesday']
        day_name = days[d]

        def to_time(mins):
            h = mins // 60
            m = mins % 60
            return f"{h:02d}:{m:02d}"

        print("SOLUTION:")
        print(f"Day: {day_name}")
        print(f"Start Time: {to_time(st)}")
        print(f"End Time: {to_time(et)}")
    else:
        print("No solution found")

schedule_meeting()