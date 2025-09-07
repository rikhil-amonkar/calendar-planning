from z3 import *

def main():
    solver = Optimize()

    day = Int('day')
    start = Int('start')

    # Day can be 0 (Monday) or 1 (Tuesday)
    solver.add(Or(day == 0, day == 1))
    # Start time in minutes from 9:00, 0 <= start <= 450 (since meeting is 30 min)
    solver.add(And(start >= 0, start <= 450))

    # Busy intervals for each day
    # Monday
    busy_ryan_mon = [
        (30, 60),  # 9:30-10:00
        (120, 180),  # 11:00-12:00
        (240, 270),  # 13:00-13:30
        (390, 420),  # 15:30-16:00
    ]
    busy_adam_mon = [
        (0, 90),  # 9:00-10:30
        (120, 270),  # 11:00-13:30
        (300, 420),  # 14:00-16:00
        (450, 480),  # 16:30-17:00
    ]
    # Tuesday
    busy_ryan_tue = [
        (150, 210),  # 11:30-12:30
        (390, 420),  # 15:30-16:00
    ]
    busy_adam_tue = [
        (0, 60),  # 9:00-10:00
        (90, 390),  # 10:30-15:30
        (420, 480),  # 16:00-17:00
    ]

    def create_constraints(busy_ryan, busy_adam):
        all_busies = busy_ryan + busy_adam
        constraints = []
        for b_start, b_end in all_busies:
            constraints.append(Or(start + 30 <= b_start, start >= b_end))
        return And(constraints)

    mon_constraints = create_constraints(busy_ryan_mon, busy_adam_mon)
    tue_constraints = create_constraints(busy_ryan_tue, busy_adam_tue)

    solver.add(Implies(day == 0, mon_constraints))
    solver.add(Implies(day == 1, tue_constraints))

    # Define priority for Adam's preference
    # Priority is 2 for Tuesday, 1 for Monday after 14:30 (330 minutes from 9:00), 0 otherwise
    priority = If(day == 1, 2, If(And(day == 0, start >= 330), 1, 0))
    solver.maximize(priority)

    if solver.check() == sat:
        model = solver.model()
        day_val = model[day].as_long()
        start_val = model[start].as_long()

        def format_time(minutes):
            hours = 9 + minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        start_time = format_time(start_val)
        end_time = format_time(start_val + 30)
        days = ["Monday", "Tuesday"]
        print(f"{days[day_val]} {start_time}:{end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()