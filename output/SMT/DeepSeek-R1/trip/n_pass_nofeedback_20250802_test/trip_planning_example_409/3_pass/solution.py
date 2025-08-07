import z3
import json

def main():
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    n_days = 12
    n_cities = len(cities)
    
    # Graph of direct flights: each city index maps to list of neighbors
    graph = {
        0: [3, 2, 1, 4],   # Hamburg: Bucharest, Helsinki, Zurich, Split
        1: [0, 2, 3, 4],    # Zurich: Hamburg, Helsinki, Bucharest, Split
        2: [0, 1, 4],       # Helsinki: Hamburg, Zurich, Split
        3: [0, 1],          # Bucharest: Hamburg, Zurich
        4: [0, 1, 2]        # Split: Hamburg, Zurich, Helsinki
    }
    
    # Precompute all directed edges from the graph
    edges = []
    for i in range(n_cities):
        for j in graph[i]:
            edges.append((i, j))
    
    # Required days per city: Hamburg(0), Zurich(1), Helsinki(2), Bucharest(3), Split(4)
    required_days = [2, 3, 2, 2, 7]
    
    # Z3 variables for each day: start city, whether we fly, and destination city
    Start = [z3.Int('Start_%d' % d) for d in range(n_days)]
    Fly = [z3.Bool('Fly_%d' % d) for d in range(n_days)]
    Dest = [z3.Int('Dest_%d' % d) for d in range(n_days)]
    
    s = z3.Solver()
    
    # City indices must be valid
    for d in range(n_days):
        s.add(Start[d] >= 0, Start[d] < n_cities)
        s.add(Dest[d] >= 0, Dest[d] < n_cities)
        # If flying, start and destination must be different
        s.add(z3.Implies(Fly[d], Start[d] != Dest[d]))
    
    # Flight constraints: if flying, the (start, dest) must be in the edges list
    for d in range(n_days):
        edge_constraints = []
        for (i, j) in edges:
            edge_constraints.append(z3.And(Start[d] == i, Dest[d] == j))
        s.add(z3.Implies(Fly[d], z3.Or(edge_constraints)))
    
    # Continuity: next day's start is current day's destination if flying, else same as current start
    for d in range(n_days - 1):
        s.add(Start[d+1] == z3.If(Fly[d], Dest[d], Start[d]))
    
    # Total days per city constraint
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            in_city = z3.Or(Start[d] == c, z3.And(Fly[d], Dest[d] == c))
            total += z3.If(in_city, 1, 0)
        s.add(total == required_days[c])
    
    # Wedding constraint: must be in Zurich on at least one of the first three days (days 1-3)
    wedding_days = []
    for d in [0, 1, 2]:  # Days 1, 2, 3 (0-indexed)
        in_zurich = z3.Or(Start[d] == 1, z3.And(Fly[d], Dest[d] == 1))
        wedding_days.append(in_zurich)
    s.add(z3.Or(wedding_days))
    
    # Conference constraints: must be in Split on day 4 (index 3) and day 10 (index 9)
    s.add(z3.Or(Start[3] == 4, z3.And(Fly[3], Dest[3] == 4)))  # Day 4
    s.add(z3.Or(Start[9] == 4, z3.And(Fly[9], Dest[9] == 4)))  # Day 10
    
    # Total flights must be 4 (because 12 days + 4 flights = 16 city-days)
    total_flights = z3.Sum([z3.If(Fly[d], 1, 0) for d in range(n_days)])
    s.add(total_flights == 4)
    
    # Solve the problem
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            start_val = m.evaluate(Start[d]).as_long()
            fly_val = m.evaluate(Fly[d])
            if fly_val:
                dest_val = m.evaluate(Dest[d]).as_long()
                places = sorted([cities[start_val], cities[dest_val]])
            else:
                places = [cities[start_val]]
            itinerary.append({"day": d+1, "place": places})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()