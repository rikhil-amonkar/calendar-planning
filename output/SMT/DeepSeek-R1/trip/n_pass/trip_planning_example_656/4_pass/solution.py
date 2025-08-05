from z3 import *

def plan_trip(n, lengths, dependencies):
    if n == 0:
        return [], 0
    if n == 1:
        return [0], lengths[0]
    
    s = Solver()
    # Use 32-bit BitVec for position variables
    position = [BitVec('pos_%i' % i, 32) for i in range(n)]
    
    # Each position must be between 0 and n-1
    for i in range(n):
        s.add(position[i] >= 0, position[i] < n)
    
    # All positions must be distinct
    s.add(Distinct(position))
    
    # Start with activity 0 and end with activity n-1
    s.add(position[0] == 0)
    s.add(position[n-1] == n-1)
    
    # Handle dependencies: activity i must come before j
    for (i, j) in dependencies:
        s.add(position[i] < position[j])
    
    if s.check() == sat:
        m = s.model()
        # Build the order array from position values
        order = [-1] * n
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

    data = json.load(sys.stdin)
    activities = data["activities"]
    n = len(activities)
    lengths = [act["length"] for act in activities]
    dependencies = data["dependencies"]
    
    dep_tuples = []
    for dep in dependencies:
        dep_tuples.append((dep["from"], dep["to"]))
    
    order, total_time = plan_trip(n, lengths, dep_tuples)
    
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