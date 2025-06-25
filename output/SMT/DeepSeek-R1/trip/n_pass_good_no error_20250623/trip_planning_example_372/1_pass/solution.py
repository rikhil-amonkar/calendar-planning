import z3
from itertools import combinations

def main():
    cities = ["Madrid", "Seville", "Porto", "Stuttgart"]
    edge_list = [("Porto", "Stuttgart"), ("Seville", "Porto"), ("Madrid", "Porto"), ("Madrid", "Seville")]
    edge_set = set()
    for edge in edge_list:
        edge_set.add(tuple(sorted(edge)))
    edge_pairs = list(edge_set)
    
    days = list(range(1, 14))
    flight_days = list(range(1, 13))
    
    in_city = {}
    for city in cities:
        in_city[city] = [z3.Bool(f"in_{city}_{d}") for d in days]
    
    flight_edge = {}
    for (A, B) in edge_pairs:
        flight_edge[(A, B)] = [z3.Bool(f"flight_{A}_{B}_{d}") for d in flight_days]
    
    s = z3.Solver()
    
    for d in days:
        idx = d - 1
        total = z3.Sum([z3.If(in_city[city][idx], 1, 0) for city in cities])
        if d < 13:
            has_flight = z3.Or([flight_edge[edge][d-1] for edge in edge_pairs])
            s.add(total == 1 + z3.If(has_flight, 1, 0))
        else:
            s.add(total == 1)
    
    for edge in edge_pairs:
        A, B = edge
        for d in flight_days:
            idx = d - 1
            s.add(flight_edge[edge][idx] == z3.And(in_city[A][idx], in_city[B][idx]))
    
    all_pairs = set(combinations(cities, 2))
    non_edges = all_pairs - set(edge_pairs)
    for (A, B) in non_edges:
        for d in days:
            idx = d - 1
            s.add(z3.Not(z3.And(in_city[A][idx], in_city[B][idx])))
    
    required_days = {
        "Madrid": 4,
        "Seville": 2,
        "Porto": 3,
        "Stuttgart": 7
    }
    for city in cities:
        total = z3.Sum([z3.If(in_city[city][d], 1, 0) for d in range(13)])
        s.add(total == required_days[city])
    
    s.add(in_city["Stuttgart"][6])
    s.add(in_city["Stuttgart"][12])
    
    s.add(z3.Or([in_city["Madrid"][d] for d in [0,1,2,3]]))
    
    flight_day_vars = []
    for d in flight_days:
        has_flight = z3.Or([flight_edge[edge][d-1] for edge in edge_pairs])
        flight_day_vars.append(z3.If(has_flight, 1, 0))
    total_flights = z3.Sum(flight_day_vars)
    s.add(total_flights == 3)
    
    if s.check() == z3.sat:
        m = s.model()
        in_city_assign = {}
        for city in cities:
            in_city_assign[city] = [m.eval(in_city[city][d]) for d in range(13)]
        
        blocks = {}
        for city in cities:
            days_present = [d+1 for d in range(13) if in_city_assign[city][d] == z3.BoolVal(True)]
            if not days_present:
                blocks[city] = []
                continue
            days_present.sort()
            segments = []
            start = days_present[0]
            end = days_present[0]
            for i in range(1, len(days_present)):
                if days_present[i] == end + 1:
                    end = days_present[i]
                else:
                    segments.append((start, end))
                    start = days_present[i]
                    end = days_present[i]
            segments.append((start, end))
            blocks[city] = segments
        
        flight_days_assign = set()
        for d in flight_days:
            for edge in edge_pairs:
                if m.eval(flight_edge[edge][d-1]) == z3.BoolVal(True):
                    flight_days_assign.add(d)
        
        itinerary = []
        for city in cities:
            for (start, end) in blocks[city]:
                if start == end:
                    day_str = f"Day {start}"
                else:
                    day_str = f"Day {start}-{end}"
                itinerary.append({"day_range": day_str, "place": city})
        
        for d in flight_days_assign:
            for city in cities:
                if m.eval(in_city[city][d-1]) == z3.BoolVal(True):
                    itinerary.append({"day_range": f"Day {d}", "place": city})
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()