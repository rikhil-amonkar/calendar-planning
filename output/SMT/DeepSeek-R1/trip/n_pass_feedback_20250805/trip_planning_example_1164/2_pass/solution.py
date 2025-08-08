from z3 import *

def main():
    s = Solver()
    n_people = 1
    n_days = 3
    n_cities = 3

    # City variables for each day (for the single person)
    c0 = Int('c0')
    c1 = Int('c1')
    c2 = Int('c2')
    c = [c0, c1, c2]

    # Stay variables for each city
    stay0 = Int('stay0')
    stay1 = Int('stay1')
    stay2 = Int('stay2')
    stays = [stay0, stay1, stay2]

    # Adjacency matrix
    adj = [
        [0, 1, 0],
        [1, 0, 1],
        [0, 1, 0]
    ]

    # City assignments constraints
    for i in range(n_days):
        s.add(And(c[i] >= 0, c[i] < n_cities))

    # Start and end constraints
    s.add(c0 == 0)
    s.add(c2 == 2)

    # Adjacency constraints between consecutive days
    for i in range(n_days - 1):
        from_city = c[i]
        to_city = c[i+1]
        # Use element-wise constraints instead of matrix indexing
        s.add(Or(
            And(from_city == 0, to_city == 1),
            And(from_city == 1, Or(to_city == 0, to_city == 2)),
            And(from_city == 2, to_city == 1)
        ))

    # Stay constraints: Count days per city using If conditions
    s.add(stay0 == Sum([If(c[i] == 0, 1, 0) for i in range(n_days)]))
    s.add(stay1 == Sum([If(c[i] == 1, 1, 0) for i in range(n_days)]))
    s.add(stay2 == Sum([If(c[i] == 2, 1, 0) for i in range(n_days)]))
    
    # Fixed stay requirements
    s.add(stay0 == 1)
    s.add(stay1 == 1)
    s.add(stay2 == 1)

    # Solve and print solution
    if s.check() == sat:
        m = s.model()
        print("Solution:")
        print(f"Day 0: City {m[c0]}")
        print(f"Day 1: City {m[c1]}")
        print(f"Day 2: City {m[c2]}")
        print(f"Stay in City 0: {m[stay0]}")
        print(f"Stay in City 1: {m[stay1]}")
        print(f"Stay in City 2: {m[stay2]}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()