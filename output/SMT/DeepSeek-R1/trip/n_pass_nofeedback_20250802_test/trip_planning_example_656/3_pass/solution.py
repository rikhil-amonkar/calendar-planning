from z3 import *

def plan_trip(n, lengths, dependencies):
    s = Solver()
    
    # Create position variables: position[i] = the index of activity i in the order
    position = [Int('pos_%i' % i) for i in range(n)]
    
    # Each position must be between 0 and n-1
    for i in range(n):
        s.add(position[i] >= 0, position[i] < n)
    
    # All positions must be distinct
    s.add(Distinct(position))
    
    # The trip must start with activity 0 and end with activity n-1
    s.add(position[0] == 0)
    s.add(position[n-1] == n-1)
    
    # Dependencies: for each (i, j) in dependencies, activity i must come before activity j
    for (i, j) in dependencies:
        s.add(position[i] < position[j])
    
    # Check for a valid solution
    if s.check() == sat:
        m = s.model()
        # Build the order array: order[k] = activity at position k
        order = [0] * n
        for i in range(n):
            pos_val = m.evaluate(position[i]).as_long()
            order[pos_val] = i
        total_time = sum(lengths)
        return order, total_time
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