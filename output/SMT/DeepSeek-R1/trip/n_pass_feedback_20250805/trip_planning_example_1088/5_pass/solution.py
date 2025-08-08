import z3
import json

def main():
    cities = ["Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    n_cities = len(cities)
    n_days = 21
    n_points = n_days + 1  # 22 points: start of day1 to end of day21

    # Flight network adjacency list
    adj = {
        0: [1, 2, 6, 7],    # Reykjavik
        1: [0, 3, 4, 5, 6, 7],  # Oslo
        2: [0, 3, 5, 7],     # Stuttgart
        3: [1, 2, 4, 7],     # Split
        4: [1, 3, 5, 7],     # Geneva
        5: [1, 2, 4],        # Porto
        6: [0, 1],           # Tallinn
        7: [0, 1, 2, 3, 4]   # Stockholm
    }

    # Create Z3 variables for each point in the sequence
    city = [z3.Int(f'city_{i}') for i in range(n_points)]
    
    s = z3.Solver()

    # Fixed constraints: Reykjavik on days 1-2
    s.add(city[0] == 0)  # Start of day1
    s.add(city[1] == 0)  # End of day1/start of day2
    s.add(city[2] == 0)  # End of day2

    # Fixed constraints: Porto on days 19-21
    s.add(city[18] == 5)  # Start of day19
    s.add(city[19] == 5)  # End of day19/start of day20
    s.add(city[20] == 5)  # End of day20/start of day21
    s.add(city[21] == 5)  # End of day21

    # Flight constraints for each day
    for d in range(n_days):
        # Non-flight option (same city)
        no_flight = (city[d] == city[d+1])
        
        # Flight options (direct connections)
        flight_options = []
        for c in adj:
            for neighbor in adj[c]:
                flight_options.append(z3.And(city[d] == c, city[d+1] == neighbor))
        
        s.add(z3.Or(no_flight, *flight_options))

    # Stockholm constraint: must appear in days 2-4 (positions 2,3,4 in sequence)
    s.add(z3.Or(city[2] == 7, city[3] == 7, city[4] == 7))

    # Total days per city (count days where city appears in start or end)
    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for d in range(n_days):
            total += z3.If(z3.Or(city[d] == c, city[d+1] == c), 1, 0)
        total_days[c] = total
        s.add(total == [2, 5, 5, 3, 2, 3, 5, 3][c])

    # Solve and output itinerary
    if s.check() == z3.sat:
        m = s.model()
        city_vals = [m.evaluate(city[i]).as_long() for i in range(n_points)]
        
        itinerary = []
        for d in range(n_days):
            c1 = cities[city_vals[d]]
            c2 = cities[city_vals[d+1]]
            places = sorted(list(set([c1, c2])))
            itinerary.append({"day": d+1, "place": places})
        
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()