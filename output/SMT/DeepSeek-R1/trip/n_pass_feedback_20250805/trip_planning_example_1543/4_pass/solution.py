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

    # Trip sequences
    trip1 = [Int(f'trip1_{i}') for i in range(max_trips_per_passenger)]
    trip2 = [Int(f'trip2_{i}') for i in range(max_trips_per_passenger)]

    # Each trip location must be valid
    for i in range(max_trips_per_passenger):
        s.add(Or([trip1[i] == loc for loc in locations]))
        s.add(Or([trip2[i] == loc for loc in locations]))

    # Consecutive trip distance constraints
    for j in range(max_trips_per_passenger):
        # Passenger 1
        s.add(Implies(And(j < n1, j == 0), 
                   dist(start_location1, trip1[j]) >= min_distance))
        s.add(Implies(And(j < n1, j > 0), 
                   dist(trip1[j-1], trip1[j]) >= min_distance))
        # Passenger 2
        s.add(Implies(And(j < n2, j == 0), 
                   dist(start_location2, trip2[j]) >= min_distance))
        s.add(Implies(And(j < n2, j > 0), 
                   dist(trip2[j-1], trip2[j]) >= min_distance))

    # Final state: both passengers must end at the same location
    final_state1 = If(n1 > 0, trip1[n1-1], start_location1)
    final_state2 = If(n2 > 0, trip2[n2-1], start_location2)
    s.add(final_state1 == final_state2)

    # Avoid same location at the same time during intermediate steps
    T = If(n1 > n2, n1, n2)  # Total time steps
    for k in range(max_total_trips):
        state1_k = If(k < n1, trip1[k], final_state1)
        state2_k = If(k < n2, trip2[k], final_state2)
        # Condition: k < T - 1 (intermediate steps)
        s.add(Implies(k < T - 1, state1_k != state2_k))

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
        trips1 = [m.evaluate(trip1[i]) for i in range(n1_val)]
        trips2 = [m.evaluate(trip2[i]) for i in range(n2_val)]
        print(f"n1 = {n1_val}")
        print(f"n2 = {n2_val}")
        print(f"Total trips = {n1_val + n2_val}")
        print(f"Passenger 1 trips: {trips1}")
        print(f"Passenger 2 trips: {trips2}")
        print(f"End location: {m.evaluate(final_state1)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()