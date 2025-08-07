from z3 import *
import json

def main():
    city_names = ["Frankfurt", "Salzburg", "Athens", "Reykjavik", "Bucharest", "Valencia", "Vienna", "Amsterdam", "Stockholm", "Riga"]
    dur = [4, 5, 5, 5, 3, 2, 5, 3, 3, 3]
    n = 10
    total_days = 29

    # Build the adjacency matrix for flights
    adj = [[False] * n for _ in range(n)]
    edges = [
        (0,5), (0,9), (0,7), (0,3), (0,4), (0,8), (0,6), (0,1),
        (1,0),
        (2,5), (2,4), (2,9), (2,8), (2,0), (2,3), (2,7), (2,6),
        (3,7), (3,0), (3,2), (3,8), (3,6),
        (4,6), (4,2), (4,7), (4,0), (4,5), (4,9),
        (5,0), (5,2), (5,7), (5,6), (5,4),
        (6,4), (6,2), (6,3), (6,0), (6,5), (6,7), (6,8), (6,9),
        (7,4), (7,2), (7,3), (7,0), (7,5), (7,6), (7,8), (7,9),
        (8,2), (8,6), (8,7), (8,3), (8,0), (8,9),
        (9,0), (9,2), (9,4), (9,6), (9,7), (9,8)
    ]
    for (i, j) in edges:
        adj[i][j] = True
        adj[j][i] = True

    allowed_edges = set()
    for i in range(n):
        for j in range(n):
            if adj[i][j]:
                allowed_edges.add((i, j))

    # Create Z3 variables
    P = [Int('P%d' % i) for i in range(n)]
    s = Solver()

    # Each P[i] is between 0 and n-1
    for i in range(n):
        s.add(And(P[i] >= 0, P[i] < n))
    s.add(Distinct(P))

    # Define cumulative sums
    cs_z3 = [Int('cs_z3_%d' % i) for i in range(n)]
    s.add(cs_z3[0] == 0)
    for i in range(1, n):
        s.add(cs_z3[i] == cs_z3[i-1] + (dur[P[i-1]] - 1))

    # Total cumulative sum at the end must be 28
    s.add(cs_z3[9] == 28)

    # For each city, define the cumulative sum at its position
    city_cs = [Int('city_cs_%d' % c) for c in range(n)]
    for c in range(n):
        cases = [cs_z3[i] for i in range(n)]
        expr = cases[0]
        for i in range(n-1, -1, -1):
            expr = If(P[i] == c, cases[i], expr)
        s.add(city_cs[c] == expr)

    # Constraints for specific cities
    # Valencia (index 5) must have cumulative sum = 4 -> start day = 1+4=5
    s.add(city_cs[5] == 4)
    # Athens (index 2): 9 <= cum_sum <= 17 -> start day between 10 and 18
    s.add(city_cs[2] >= 9, city_cs[2] <= 17)
    # Vienna (index 6): 1 <= cum_sum <= 9 -> start day between 2 and 10
    s.add(city_cs[6] >= 1, city_cs[6] <= 9)
    # Riga (index 9): 15 <= cum_sum <= 19 -> start day between 16 and 20
    s.add(city_cs[9] >= 15, city_cs[9] <= 19)
    # Stockholm (index 8): cum_sum <= 2 -> start day <= 3
    s.add(city_cs[8] <= 2)

    # Flight constraints: consecutive cities must have a direct flight
    for i in range(n-1):
        edge_ok = Or([And(P[i] == a, P[i+1] == b) for (a, b) in allowed_edges])
        s.add(edge_ok)

    # Check and get the model
    if s.check() == sat:
        model = s.model()
        perm = [model.eval(P[i]).as_long() for i in range(n)]
        cs_vals = [model.eval(cs_z3[i]).as_long() for i in range(n)]
        
        # Map city index to its start and end day
        city_start = [0] * n
        city_end = [0] * n
        for idx in range(n):
            c = perm[idx]
            start_day = 1 + cs_vals[idx]
            city_start[c] = start_day
            city_end[c] = start_day + dur[c] - 1
        
        # Generate itinerary
        itinerary = []
        for day in range(1, total_days+1):
            for c in range(n):
                if day >= city_start[c] and day <= city_end[c]:
                    itinerary.append({"day": day, "place": city_names[c]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()