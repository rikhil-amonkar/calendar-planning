from z3 import Solver, Int, Or, And

def main():
    s = Solver()
    start = Int('start')
    s.add(start >= 0, start <= 450)  # 450 because meeting duration is 30 minutes (17:00 - 0.5h = 16:30)

    # Convert busy times to minutes from 9:00
    andrea_busy = [[30, 90], [270, 330]]
    ruth_busy = [[210, 240], [360, 390]]
    steven_busy = [[60, 90], [120, 150], [180, 210], [270, 300], [360, 420]]
    kyle_busy = [[0, 30], [90, 180], [210, 240], [270, 360], [390, 420], [450, 480]]
    elijah_busy = [[0, 120], [150, 240], [270, 300], [390, 420], [450, 480]]
    lori_busy = [[0, 30], [60, 150], [180, 270], [300, 420], [450, 480]]

    # Grace has no meetings, so no constraints

    # Function to add constraints for a participant
    def add_participant_constraints(busy_intervals):
        constraints = []
        for interval in busy_intervals:
            a, b = interval
            constraints.append(Or(start + 30 <= a, start >= b))
        s.add(And(constraints))

    add_participant_constraints(andrea_busy)
    add_participant_constraints(ruth_busy)
    add_participant_constraints(steven_busy)
    add_participant_constraints(kyle_busy)
    add_participant_constraints(elijah_busy)
    add_participant_constraints(lori_busy)

    if s.check() == z3.sat:
        model = s.model()
        start_minutes = model[start].as_long()
        # Convert minutes back to time string
        hours = 9 + start_minutes // 60
        minutes = start_minutes % 60
        start_time = f"{hours}:{minutes:02d}"
        end_minutes = start_minutes + 30
        end_hours = 9 + end_minutes // 60
        end_minutes = end_minutes % 60
        end_time = f"{end_hours}:{end_minutes:02d}"
        print(f"Monday, {start_time}, {end_time}")
    else:
        print("No solution found")

if __name__ == "__main__":
    import z3
    main()