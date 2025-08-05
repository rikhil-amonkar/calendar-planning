from z3 import *

def plan_trip(n, lengths, dependencies):
    s = Solver()
    
    # Create order variables: order[0], order[1], ..., order[n-1]
    order = [Int('order_%i' % i) for i in range(n)]
    
    # Constraint: the order must be a permutation of [0, n-1]
    s.add(Distinct(order))
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    
    # The trip must start with activity 0 and end with activity n-1
    s.add(order[0] == 0)
    s.add(order[n-1] == n-1)
    
    # Dependencies: for each (i, j) in dependencies, activity i must come before activity j
    for (i, j) in dependencies:
        # Find positions of activity i and activity j in the order
        pos_i = Int('pos_%i' % i)
        pos_j = Int('pos_%i' % j)
        # Constraint: pos_i < pos_j
        s.add(pos_i < pos_j)
        # Now, link pos_i and pos_j to the order: forall k in [0, n-1], (order[k] == i) => (pos_i == k), similarly for j
        s.add(Or([And(order[k] == i, pos_i == k) for k in range(n)]))
        s.add(Or([And(order[k] == j, pos_j == k) for k in range(n)]))
    
    # Create an array to store the lengths of activities
    length_arr = Array('lengths', IntSort(), IntSort())
    for idx, l in enumerate(lengths):
        length_arr = Store(length_arr, idx, l)
    
    # Prefix sum array: prefix_sum[0] = 0, prefix_sum[i] = prefix_sum[i-1] + length of activity at order[i-1]
    prefix_sum = [0] * (n+1)
    prefix_sum[0] = 0
    for i in range(1, n+1):
        # Get the activity index at position i-1 in the order
        activity_index = order[i-1]
        # Get the length of that activity from the Z3 array
        activity_length = length_arr[activity_index]
        prefix_sum[i] = prefix_sum[i-1] + activity_length
    
    # The total trip time is prefix_sum[n]
    total_time = prefix_sum[n]
    
    # Start times: for activity at order[i], it starts at prefix_sum[i] and ends at prefix_sum[i+1]
    start_times = [Int('start_%i' % i) for i in range(n)]
    for i in range(n):
        # The activity at order[i] is the i-th in the sequence, so it starts at prefix_sum[i] and ends at prefix_sum[i+1]
        # But note: the activity index is order[i]. We have a start time for each activity index.
        # So for activity j, we need to relate: when j appears at position k, then start_times[j] = prefix_sum[k]
        # We can write: for each activity j, there exists a k such that order[k] == j and start_times[j] = prefix_sum[k]
        # Instead, we can use:
        #   s.add(Or([And(order[k] == j, start_times[j] == prefix_sum[k]) for k in range(n)]))
        # But we already have the prefix_sum defined in terms of order. Alternatively, we can define the start time of an activity j as:
        #   start_times[j] = prefix_sum[k] where k is the position of j in the order.
        pass  # We don't use start_times in the objective, so we skip if not needed for objective.
    
    # We might not need the start_times for minimization? The problem says to minimize total time.
    # But the constraints above already link the start times implicitly? 
    # Actually, the problem does not require outputting start times, only the order and total time.
    # So we can skip creating start_times variables if not needed for output.
    
    # Objective: minimize total_time
    s.minimize(total_time)
    
    if s.check() == sat:
        m = s.model()
        order_vals = [m.evaluate(order[i]).as_long() for i in range(n)]
        total_time_val = m.evaluate(total_time).as_long()
        return order_vals, total_time_val
    else:
        return None, None

def main():
    import json
    import sys

    # Read the input data from stdin
    data = json.load(sys.stdin)
    activities = data["activities"]
    n = len(activities)
    lengths = [act["length"] for act in activities]
    dependencies = data["dependencies"]
    
    # Convert dependencies: from list of dicts to list of tuples (i, j)
    dep_tuples = []
    for dep in dependencies:
        dep_tuples.append((dep["from"], dep["to"]))
    
    # Call the planning function
    order, total_time = plan_trip(n, lengths, dep_tuples)
    
    # Output the result
    if order is None:
        print(json.dumps({"error": "No solution found"}))
    else:
        result = {
            "order": order,
            "total_time": total_time
        }
        print(json.dumps(result))

if __name__ == '__main__':
    main()