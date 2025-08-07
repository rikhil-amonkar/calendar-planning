from z3 import *

def main():
    s = Solver()
    n_people = 1
    n_days = 3
    n_cities = 3
    required_stays = [1, 1, 1]

    # Adjacency matrix
    adj = [
        [0, 1, 0],
        [1, 0, 1],
        [0, 1, 0]
    ]

    # Precompute allowed transitions
    allowed_pairs = []
    for i in range(n_cities):
        for j in range(n_cities):
            if adj[i][j] == 1:
                allowed_pairs.append((i, j))

    # City variables for each day
    c = [Int(f'c_{i}') for i in range(n_days)]
    
    # Stay variables for each city
    stays = [Int(f'stay_{i}') for i in range(n_cities)]

    # City assignments constraints
    for i in range(n_days):
        s.add(And(c[i] >= 0, c[i] < n_cities))

    # Start and end constraints
    s.add(c[0] == 0)
    s.add(c[n_days-1] == 2)

    # Adjacency constraints
    for i in range(n_days - 1):
        s.add(Or([And(c[i] == pair[0], c[i+1] == pair[1]) for pair in allowed_pairs]))

    # Stay constraints
    for j in range(n_cities):
        s.add(stays[j] == Sum([If(c[i] == j, 1, 0) for i in range(n_days)]))
    
    # Apply stay requirements
    for j in range(n_cities):
        s.add(stays[j] == required_stays[j])

    # Solve and print solution
    if s.check() == sat:
        m = s.model()
        print("Solution:")
        for i in range(n_days):
            print(f"Day {i}: City {m[c[i]].as_long()}")
        for j in range(n_cities):
            print(f"Stay in City {j}: {m[stays[j]].as_long()}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()