import z3
import json

def main():
    CityNames = ["Venice", "Barcelona", "Copenhagen", "Lyon", "Reykjavik", "Dubrovnik", "Athens", "Tallinn", "Munich"]
    Durations = [4, 3, 4, 4, 4, 5, 2, 5, 3]  # index-aligned with CityNames

    # Build directed flight graph
    edges = set()
    # Add the directed flight: Reykjavik -> Athens
    edges.add((4, 6))  # Reykjavik (4) -> Athens (6)
    
    # Bidirectional pairs: add both directions
    bidirectional_pairs = [
        (2, 6), (2, 5), (8, 7), (2, 8), (0, 8), (6, 5), (0, 6), (3, 1), (2, 4), (4, 8),
        (6, 8), (3, 8), (1, 4), (0, 2), (1, 5), (3, 0), (5, 8), (1, 6), (2, 1), (0, 1),
        (1, 8), (1, 7), (2, 7)
    ]
    for a, b in bidirectional_pairs:
        edges.add((a, b))
        edges.add((b, a))
    
    # Initialize Z3 variables
    s = z3.Solver()
    city = [z3.Int(f"city_{i}") for i in range(9)]
    start = [z3.Int(f"start_{i}") for i in range(9)]
    end = [z3.Int(f"end_{i}") for i in range(9)]
    
    # Constraints
    s.add(start[0] == 1)
    s.add(end[8] == 26)
    
    for i in range(9):
        s.add(end[i] == start[i] + z3.If(
            city[i] == 0, Durations[0],
            z3.If(city[i] == 1, Durations[1],
            z3.If(city[i] == 2, Durations[2],
            z3.If(city[i] == 3, Durations[3],
            z3.If(city[i] == 4, Durations[4],
            z3.If(city[i] == 5, Durations[5],
            z3.If(city[i] == 6, Durations[6],
            z3.If(city[i] == 7, Durations[7],
            Durations[8])))))))) - 1)
        )
    
    for i in range(1, 9):
        s.add(start[i] == end[i-1])
    
    s.add(z3.Distinct(city))
    for i in range(9):
        s.add(city[i] >= 0)
        s.add(city[i] <= 8)
    
    for i in range(8):
        constraints = []
        for a, b in edges:
            constraints.append(z3.And(city[i] == a, city[i+1] == b))
        s.add(z3.Or(constraints))
    
    for j in range(9):
        s.add(z3.Implies(city[j] == 1, z3.And(start[j] <= 12, end[j] >= 10)))  # Barcelona
        s.add(z3.Implies(city[j] == 2, z3.And(start[j] <= 10, end[j] >= 7)))   # Copenhagen
        s.add(z3.Implies(city[j] == 5, z3.And(start[j] <= 20, end[j] >= 16)))  # Dubrovnik
    
    if s.check() == z3.sat:
        m = s.model()
        city_order = [m.evaluate(city[i]).as_long() for i in range(9)]
        start_days = [m.evaluate(start[i]).as_long() for i in range(9)]
        end_days = [m.evaluate(end[i]).as_long() for i in range(9)]
        
        itinerary_list = []
        itinerary_list.append({
            "day_range": f"Day {start_days[0]}-{end_days[0]}",
            "place": CityNames[city_order[0]]
        })
        
        for i in range(8):
            flight_day = end_days[i]
            itinerary_list.append({
                "day_range": f"Day {flight_day}",
                "place": CityNames[city_order[i]]
            })
            itinerary_list.append({
                "day_range": f"Day {flight_day}",
                "place": CityNames[city_order[i+1]]
            })
            itinerary_list.append({
                "day_range": f"Day {start_days[i+1]}-{end_days[i+1]}",
                "place": CityNames[city_order[i+1]]
            })
        
        result = {"itinerary": itinerary_list}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()