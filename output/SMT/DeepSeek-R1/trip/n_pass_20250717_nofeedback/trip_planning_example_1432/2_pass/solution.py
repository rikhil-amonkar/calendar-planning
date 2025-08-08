from z3 import *

def main():
    # Sample data for testing
    n_locations = 3
    start_arr = [0, 0, 0]
    duration_arr = [1, 1, 1]
    travel_matrix = [
        [0, 1, 1],
        [1, 0, 1],
        [1, 1, 0]
    ]
    n = 3  # Number of activities to schedule

    # Create Z3 solver
    s = Solver()

    # Activity start times and completion times
    S = [Int(f'S{i}') for i in range(n)]
    C = [Int(f'C{i}') for i in range(n)]
    
    # Order of locations visited
    order = [Int(f'order{i}') for i in range(n)]

    # Uninterpreted functions for start times, durations, and travel times
    start_func = Function('start_func', IntSort(), IntSort())
    duration_func = Function('duration_func', IntSort(), IntSort())
    travel_func = Function('travel_func', IntSort(), IntSort(), IntSort())

    # Define function mappings
    for j in range(n_locations):
        s.add(start_func(j) == start_arr[j])
        s.add(duration_func(j) == duration_arr[j])
    
    for r in range(n_locations):
        for c in range(n_locations):
            s.add(travel_func(r, c) == travel_matrix[r][c])

    # Constraints on order variables
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n_locations)
    s.add(Distinct(order))

    # Schedule constraints
    for i in range(n):
        # Start time must be at least the location's opening time
        s.add(S[i] >= start_func(order[i]))
        # Activity duration matches location's duration
        s.add(C[i] == duration_func(order[i]))

    # First activity starts at its location's opening time
    s.add(S[0] == start_func(order[0]))

    # Subsequent activities start after previous activity completes plus travel
    for i in range(1, n):
        travel_time = travel_func(order[i-1], order[i])
        s.add(S[i] >= S[i-1] + C[i-1] + travel_time)

    # Check satisfiability and print solution
    if s.check() == sat:
        m = s.model()
        print("Found solution:")
        for i in range(n):
            loc = m.evaluate(order[i]).as_long()
            start = m.evaluate(S[i]).as_long()
            end = start + m.evaluate(C[i]).as_long()
            print(f"Activity {i}: Location {loc} (Start: {start}, End: {end})")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()