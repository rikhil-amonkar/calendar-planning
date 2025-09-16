import z3
import json

def main():
    cities = ["Hamburg", "Zurich", "Helsinki", "Bucharest", "Split"]
    n_days = 12
    n_cities = len(cities)
    
    graph = {
        0: [3, 2, 1, 4],   # Hamburg: Bucharest, Helsinki, Zurich, Split
        1: [0, 2, 3, 4],    # Zurich: Hamburg, Helsinki, Bucharest, Split
        2: [1, 0, 4],       # Helsinki: Zurich, Hamburg, Split
        3: [0, 1],           # Bucharest: Hamburg, Zurich
        4: [1, 2, 0]        # Split: Zurich, Helsinki, Hamburg
    }
    
    edges = []
    for i in range(n_cities):
        for j in graph[i]:
            edges.append((i, j))
    
    Start = [z3.Int('Start_%d' % d) for d in range(n_days)]
    Fly = [z3.Bool('Fly_%d' % d) for d in range(n_days)]
    Dest = [z3.Int('Dest_%d' % d) for d in range(n_days)]
    
    s = z3.Solver()
    
    for d in range(n_days):
        s.add(Start[d] >= 0, Start[d] < n_cities)
        s.add(Dest[d] >= 0, Dest[d] < n_cities)
        s.add(z3.Implies(Fly[d], Start[d] != Dest[d]))
        
        conds = []
        for (i, j) in edges:
            conds.append(z3.And(Start[d] == i, Dest[d] == j))
        s.add(z3.Implies(Fly[d], z3.Or(conds)))
        
        if d < n_days - 1:
            s.add(Start[d+1] == z3.If(Fly[d], Dest[d], Start[d]))
    
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            in_dc = z3.Or(Start[d] == c, z3.And(Fly[d], Dest[d] == c))
            total += z3.If(in_dc, 1, 0)
        total_days[c] = total
    
    s.add(total_days[0] == 2)  # Hamburg
    s.add(total_days[1] == 3)  # Zurich
    s.add(total_days[2] == 2)  # Helsinki
    s.add(total_days[3] == 2)  # Bucharest
    s.add(total_days[4] == 7)  # Split
    
    zurich_days = []
    for d in [0, 1, 2]:
        in_d = z3.Or(Start[d] == 1, z3.And(Fly[d], Dest[d] == 1))
        zurich_days.append(in_d)
    s.add(z3.Or(zurich_days))
    
    for d in [3, 9]:
        in_d = z3.Or(Start[d] == 4, z3.And(Fly[d], Dest[d] == 4))
        s.add(in_d)
    
    if s.check() == z3.sat:
        m = s.model()
        itinerary = []
        for d in range(n_days):
            start_val = m.eval(Start[d]).as_long()
            fly_val = m.eval(Fly[d])
            if fly_val:
                dest_val = m.eval(Dest[d]).as_long()
                cities_today = sorted([cities[start_val], cities[dest_val]])
            else:
                cities_today = [cities[start_val]]
            itinerary.append({"day": d+1, "place": cities_today})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()