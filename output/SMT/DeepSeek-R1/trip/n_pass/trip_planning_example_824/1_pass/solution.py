from z3 import *
import json

def main():
    # Cities: Berlin, Split, Lyon, Lisbon, Bucharest, Riga, Tallinn
    city_names = ["Berlin", "Split", "Lyon", "Lisbon", "Bucharest", "Riga", "Tallinn"]
    durations = [5, 3, 5, 3, 3, 5, 4]
    n = 7  # number of cities/stays

    # Adjacency matrix for direct flights (undirected)
    graph = [
        [0, 1, 0, 1, 0, 1, 1],  # Berlin (0)
        [1, 0, 1, 0, 0, 0, 0],  # Split (1)
        [0, 1, 0, 1, 1, 0, 0],  # Lyon (2)
        [1, 0, 1, 0, 1, 1, 0],  # Lisbon (3)
        [0, 0, 1, 1, 0, 1, 0],  # Bucharest (4)
        [1, 0, 0, 1, 1, 0, 1],  # Riga (5)
        [1, 0, 0, 0, 0, 1, 0]   # Tallinn (6)
    ]

    s = [Int('s_%d' % i) for i in range(n)]
    e = [Int('e_%d' % i) for i in range(n)]
    city = [Int('city_%d' % i) for i in range(n)]

    solver = Solver()

    # Each city appears exactly once
    solver.add(Distinct(city))
    for i in range(n):
        solver.add(And(city[i] >= 0, city[i] < n))

    # First city is Berlin (index0)
    solver.add(city[0] == 0)

    # Start of first stay is 1
    solver.add(s[0] == 1)
    # End of last stay is 22
    solver.add(e[n-1] == 22)

    # For each stay, the end day is start + duration - 1
    for i in range(n):
        # duration for the city of stay i
        dur = durations[city[i]]
        solver.add(e[i] == s[i] + dur - 1)

    # The start of next stay is the end of the current stay
    for i in range(1, n):
        solver.add(s[i] == e[i-1])

    # Fixed events
    for i in range(n):
        # Bucharest (index4) must be from day13 to day15
        solver.add(If(city[i] == 4, And(s[i] == 13, e[i] == 15), True))
        # Lyon (index2) must include at least one day in [7,11]
        solver.add(If(city[i] == 2, And(s[i] <= 11, e[i] >= 7), True))

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        c1 = city[i]
        c2 = city[i+1]
        solver.add(graph[c1][c2] == 1)

    if solver.check() == sat:
        model = solver.model()
        city_seq = [model[city[i]].as_long() for i in range(n)]
        start_days = [model[s[i]].as_long() for i in range(n)]
        end_days = [model[e[i]].as_long() for i in range(n)]

        itinerary_list = []
        for i in range(n):
            c = city_names[city_seq[i]]
            start = start_days[i]
            end = end_days[i]
            # Add the continuous range for the stay
            itinerary_list.append({"day_range": f"Day {start}-{end}", "place": c})
            # If not the first stay, add the flight day (arrival) as a separate entry
            if i > 0:
                itinerary_list.append({"day_range": f"Day {start}", "place": c})
            # If not the last stay, add the flight day (departure) as a separate entry
            if i < n-1:
                itinerary_list.append({"day_range": f"Day {end}", "place": c})
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()