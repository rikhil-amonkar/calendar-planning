from z3 import *

def main():
    # Example data
    n = 4
    budget = 100
    graph = [
        [0, 10, 15, 20],
        [10, 0, 35, 25],
        [15, 35, 0, 30],
        [20, 25, 30, 0]
    ]

    # Define a function to get cost between two cities using symbolic indices
    def cost(i, j):
        expr = None
        for a in range(n):
            for b in range(n):
                if expr is None:
                    expr = graph[a][b]
                else:
                    expr = If(And(i == a, j == b), graph[a][b], expr)
        return expr

    # Create Z3 variables for cities
    cities = [Int('city_%d' % i) for i in range(n)]
    s = Solver()

    # Each city must be between 0 and n-1
    for i in range(n):
        s.add(cities[i] >= 0, cities[i] < n)

    # All cities must be different
    s.add(Distinct(cities))

    # Calculate total cost of the tour
    total_cost = 0
    for k in range(n):
        c1 = cities[k]
        c2 = cities[(k + 1) % n]
        total_cost += cost(c1, c2)

    s.add(total_cost <= budget)

    # Check for a solution and print results
    if s.check() == sat:
        m = s.model()
        tour = [m.evaluate(cities[i]) for i in range(n)]
        total_cost_val = m.evaluate(total_cost)
        print("Tour:", tour)
        print("Total cost:", total_cost_val)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()