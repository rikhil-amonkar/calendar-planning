from z3 import *

def main():
    # Input data
    n_activities = 3
    activity_durations = [1, 1, 1]
    time_windows = [
        (0, 10),   # Activity 0
        (0, 10),   # Activity 1
        (0, 10),   # Activity 2
    ]
    travel_time = [
        [0, 1, 1],  # From activity 0
        [1, 0, 1],  # From activity 1
        [1, 1, 0],  # From activity 2
    ]
    n_pass = 1
    start_depot = 0
    end_depot = 0
    max_time = 10

    # Create Z3 solver
    s = Solver()

    # Sequence variables: sequence of activities (including start/end depots)
    n = n_activities + 2  # Including start and end depots
    seq = [Int(f'seq_{i}') for i in range(n)]
    
    # Start times for each activity in the sequence
    start = [Int(f'start_{i}') for i in range(n)]

    # Create Z3 arrays for time windows
    lower_arr = Array('lower', IntSort(), IntSort())
    upper_arr = Array('upper', IntSort(), IntSort())
    
    # Depot time window: [0, max_time]
    s.add(lower_arr[0] == 0)
    s.add(upper_arr[0] == max_time)
    
    # Set time windows for activities (1-indexed)
    for j in range(n_activities):
        s.add(lower_arr[j+1] == time_windows[j][0])
        s.add(upper_arr[j+1] == time_windows[j][1])

    # Create Z3 array for durations
    durations_arr = Array('durations', IntSort(), IntSort())
    durations = [0]  # start depot
    durations.extend(activity_durations)  # actual activities
    durations.append(0)  # end depot
    for idx, d in enumerate(durations):
        s.add(durations_arr[idx] == d)

    # Create Z3 function for travel times
    travel_func = Function('travel', IntSort(), IntSort(), IntSort())
    
    # Total nodes including depot
    n_total = n_activities + 1  # Depot (0) + activities (1 to n_activities)
    
    # Set travel times
    for i in range(n_total):
        for j in range(n_total):
            if i == 0 and j == 0:
                s.add(travel_func(i, j) == 0)  # Depot to depot
            elif i == 0:
                s.add(travel_func(i, j) == 1)  # Depot to activity
            elif j == 0:
                s.add(travel_func(i, j) == 1)  # Activity to depot
            else:
                # Activity to activity: use provided travel time matrix
                s.add(travel_func(i, j) == travel_time[i-1][j-1])

    # Constraints

    # 1. Start and end depots are fixed
    s.add(seq[0] == start_depot)
    s.add(seq[n-1] == end_depot)

    # 2. All activities (excluding depots) are a permutation
    s.add(Distinct(seq[1:-1]))
    for i in range(1, n-1):
        s.add(seq[i] >= 1)
        s.add(seq[i] <= n_activities)

    # 3. Time windows using Z3 arrays
    for i in range(n):
        a = seq[i]
        s.add(start[i] >= lower_arr[a])
        s.add(start[i] <= upper_arr[a])

    # 4. Sequence timing constraints (FIXED: use >= instead of ==)
    for i in range(n-1):
        current_act = seq[i]
        next_act = seq[i+1]
        
        # Get duration of current activity
        duration_i = durations_arr[current_act]
        
        # Get travel time using Z3 function
        travel_time_i = travel_func(current_act, next_act)
        
        # Next start time >= current start + duration + travel time
        s.add(start[i+1] >= start[i] + duration_i + travel_time_i)

    # 5. Total time constraint
    s.add(start[n-1] <= max_time)

    # Solve and print solution
    if s.check() == sat:
        m = s.model()
        seq_sol = [m.evaluate(seq[i]).as_long() for i in range(n)]
        start_sol = [m.evaluate(start[i]).as_long() for i in range(n)]
        print("Sequence:", seq_sol)
        print("Start times:", start_sol)
    else:
        print("No solution found")

if __name__ == '__main__':
    main()