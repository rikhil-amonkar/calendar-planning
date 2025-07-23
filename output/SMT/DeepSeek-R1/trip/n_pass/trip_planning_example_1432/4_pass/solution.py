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

    # Activity start times
    S = [Int(f'S{i}') for i in range(n)]
    
    # Order of locations visited
    order = [Int(f'order{i}') for i in range(n)]

    # Uninterpreted functions for location properties
    start_func = Function('start_func', IntSort(), IntSort())
    duration_func = Function('duration_func', IntSort(), IntSort())
    travel_func = Function('travel_func', IntSort(), IntSort(), IntSort())

    # Define function mappings from sample data
    for j in range(n_locations):
        s.add(start_func(j) == start_arr[j])
        s.add(duration_func(j) == duration_arr[j])
    
    for r in range(n_locations):
        for c in range(n_locations):
            s.add(travel_func(r, c) == travel_matrix[r][c])

    # Order must be valid location indices
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n_locations)
    
    # All locations must be distinct
    s.add(Distinct(order))

    # Activity constraints
    for i in range(n):
        # Start time must be at least location's opening time
        s.add(S[i] >= start_func(order[i]))

    # Subsequent activities must account for previous activity duration and travel time
    for i in range(1, n):
        prev_loc = order[i-1]
        curr_loc = order[i]
        travel_time = travel_func(prev_loc, curr_loc)
        activity_duration = duration_func(prev_loc)
        s.add(S[i] >= S[i-1] + activity_duration + travel_time)

    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        print("Found solution:")
        for i in range(n):
            loc = m.evaluate(order[i]).as_long()
            start_val = m.evaluate(S[i]).as_long()
            duration_val = duration_arr[loc]  # Safe concrete lookup
            print(f"Activity {i}: Location {loc} (Start: {start_val}, End: {start_val + duration_val})")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()