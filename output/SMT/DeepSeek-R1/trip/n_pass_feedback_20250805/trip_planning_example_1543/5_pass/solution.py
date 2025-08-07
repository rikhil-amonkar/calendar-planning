from z3 import *

def main():
    # Given data
    locations = [0, 1, 2, 3]
    start_location1 = 0
    start_location2 = 3
    distance_matrix = [
        [0, 20, 40, 60],
        [20, 0, 30, 50],
        [40, 30, 0, 70],
        [60, 50, 70, 0]
    ]
    min_distance = 10
    max_trips_per_passenger = 10
    max_total_trips = 15
    max_time_steps = max_total_trips  # Total time steps (0 to 15)

    # Create solver
    s = Solver()

    # Define distance function
    dist = Function('dist', IntSort(), IntSort(), IntSort())
    for i in locations:
        for j in locations:
            s.add(dist(i, j) == distance_matrix[i][j])

    # Number of trips for each passenger
    n1 = Int('n1')
    n2 = Int('n2')
    s.add(n1 >= 0, n1 <= max_trips_per_passenger)
    s.add(n2 >= 0, n2 <= max_trips_per_passenger)
    s.add(n1 + n2 <= max_total_trips, n1 + n2 > 0)

    # State arrays: s1[t] and s2[t] for t in [0, max_time_steps]
    s1 = [Int(f's1_{t}') for t in range(max_time_steps + 1)]
    s2 = [Int(f's2_{t}') for t in range(max_time_steps + 1)]

    # Initial state constraints
    s.add(s1[0] == start_location1)
    s.add(s2[0] == start_location2)

    # State transitions for each time step
    for t in range(1, max_time_steps + 1):
        # Passenger 1: If trips remaining, move to a valid location with sufficient distance
        move_cond1 = t <= n1
        move_loc1 = Int(f'move1_{t}')
        s.add(If(move_cond1,
                 And(Or([move_loc1 == loc for loc in locations]),
                     dist(s1[t - 1], move_loc1) >= min_distance,
                     s1[t] == move_loc1),
                 s1[t] == s1[t - 1]))  # No move if no trips left

        # Passenger 2: Similar constraints
        move_cond2 = t <= n2
        move_loc2 = Int(f'move2_{t}')
        s.add(If(move_cond2,
                 And(Or([move_loc2 == loc for loc in locations]),
                     dist(s2[t - 1], move_loc2) >= min_distance,
                     s2[t] == move_loc2),
                 s2[t] == s2[t - 1]))

    # Final meeting constraint at the last time step
    s.add(s1[max_time_steps] == s2[max_time_steps])

    # Intermediate location constraints: Must be different until both finish trips
    max_active = If(n1 > n2, n1, n2)  # Time when the last passenger finishes
    for t in range(max_time_steps):  # t from 0 to 14
        # Only require different locations if t < max_active (both still active)
        s.add(Implies(t < max_active, s1[t] != s2[t]))

    # Minimize total trips
    total_trips = n1 + n2
    opt = Optimize()
    opt.add(s.assertions())
    opt.minimize(total_trips)

    # Check and print solution
    if opt.check() == sat:
        m = opt.model()
        n1_val = m.evaluate(n1).as_long()
        n2_val = m.evaluate(n2).as_long()
        print(f"n1 = {n1_val}")
        print(f"n2 = {n2_val}")
        print(f"Total trips = {n1_val + n2_val}")
        # Print locations at each step up to max_active
        max_active_val = max(n1_val, n2_val)
        print("Passenger 1 locations:")
        for t in range(max_active_val + 1):
            print(f"  t={t}: {m.evaluate(s1[t])}")
        print("Passenger 2 locations:")
        for t in range(max_active_val + 1):
            print(f"  t={t}: {m.evaluate(s2[t])}")
        print(f"Final meeting at t={max_time_steps}: location {m.evaluate(s1[max_time_steps])}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()