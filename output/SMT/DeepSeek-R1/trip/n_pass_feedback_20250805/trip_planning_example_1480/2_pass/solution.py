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

    # Activity index mapping: 
    #   seq[0] = start_depot
    #   seq[1..n_activities] = actual activities
    #   seq[n-1] = end_depot
    activities = list(range(n_activities))
    activity_to_index = {a: i+1 for i, a in enumerate(activities)}
    index_to_activity = {i+1: a for i, a in enumerate(activities)}
    
    # Create Z3 array for durations
    #   Includes depots: start_depot and end_depot have duration 0
    durations_arr = Array('durations', IntSort(), IntSort())
    durations = [0]  # start depot
    durations.extend(activity_durations)  # actual activities
    durations.append(0)  # end depot
    for idx, d in enumerate(durations):
        s.add(durations_arr[idx] == d)

    # Create Z3 array for travel times (flattened for simplicity)
    travel_arr = Array('travel', IntSort(), IntSort())
    travel_list = []
    for i in range(len(travel_time)):
        for j in range(len(travel_time[i])):
            travel_list.append(travel_time[i][j])
    for idx, t in enumerate(travel_list):
        s.add(travel_arr[idx] == t)

    # Constraints

    # 1. Start and end depots are fixed
    s.add(seq[0] == start_depot)
    s.add(seq[n-1] == end_depot)

    # 2. All activities (excluding depots) are a permutation
    s.add(Distinct(seq[1:-1]))
    for i in range(1, n-1):
        s.add(seq[i] >= 1)
        s.add(seq[i] <= n_activities)

    # 3. Time windows and dependencies
    for i in range(n):
        # Map sequence index to activity index for constraints
        if i == 0 or i == n-1:
            # Depot: time window [0, max_time]
            s.add(start[i] >= 0)
            s.add(start[i] <= max_time)
        else:
            # Actual activity: use its time window
            act_index = seq[i] - 1  # Convert to 0-indexed activity
            s.add(start[i] >= time_windows[act_index][0])
            s.add(start[i] <= time_windows[act_index][1])

    # 4. Sequence timing constraints
    for i in range(n-1):
        # Travel time from current to next activity
        # Flattened index: current * n_activities + next (since depots are 0)
        current_act = seq[i]
        next_act = seq[i+1]
        travel_index = current_act * (n_activities + 1) + next_act
        travel_time_i = travel_arr[travel_index]
        
        # Duration of current activity
        duration_i = durations_arr[seq[i]]
        
        # Next start time = current start + current duration + travel time
        s.add(start[i+1] == start[i] + duration_i + travel_time_i)

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