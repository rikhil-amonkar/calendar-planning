import z3
import json

def main():
    cities = ["Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva", "Porto", "Tallinn", "Stockholm"]
    n_cities = len(cities)
    n_days = 21

    adj = {
        0: [1, 2, 6, 7],
        1: [0, 3, 4, 5, 6, 7],
        2: [0, 3, 5, 7],
        3: [1, 2, 4, 7],
        4: [1, 3, 5, 7],
        5: [1, 2, 4],
        6: [0, 1],
        7: [0, 1, 2, 3, 4]
    }

    start = [z3.Int(f'start_{i}') for i in range(n_days)]
    end = [z3.Int(f'end_{i}') for i in range(n_days)]

    s = z3.Solver()

    s.add(start[0] == 0)
    s.add(end[0] == 0)

    for i in range(1, n_days):
        s.add(start[i] == end[i-1])

    for i in range(n_days):
        flight_ok = []
        flight_ok.append(start[i] == end[i])
        for c in range(n_cities):
            if c in adj:
                for neighbor in adj[c]:
                    flight_ok.append(z3.And(start[i] == c, end[i] == neighbor))
        s.add(z3.Or(flight_ok))

    s.add(z3.Or(start[18] == 5, end[18] == 5))
    s.add(z3.Or(start[19] == 5, end[19] == 5))
    s.add(z3.Or(start[20] == 5, end[20] == 5))

    stockholm_constraint = z3.Or(
        start[1] == 7, end[1] == 7,
        start[2] == 7, end[2] == 7,
        start[3] == 7, end[3] == 7
    )
    s.add(stockholm_constraint)

    total_days = [0] * n_cities
    for c in range(n_cities):
        total = 0
        for i in range(n_days):
            total += z3.If(z3.Or(start[i] == c, end[i] == c), 1, 0)
        total_days[c] = total

    s.add(total_days[0] == 2)
    s.add(total_days[1] == 5)
    s.add(total_days[2] == 5)
    s.add(total_days[3] == 3)
    s.add(total_days[4] == 2)
    s.add(total_days[5] == 3)
    s.add(total_days[6] == 5)
    s.add(total_days[7] == 3)

    if s.check() == z3.sat:
        m = s.model()
        start_vals = [m.evaluate(start[i]).as_long() for i in range(n_days)]
        end_vals = [m.evaluate(end[i]).as_long() for i in range(n_days)]
        
        itinerary = []
        for i in range(n_days):
            day = i + 1
            city_start = cities[start_vals[i]]
            city_end = cities[end_vals[i]]
            places = set()
            places.add(city_start)
            places.add(city_end)
            itinerary.append({"day": day, "place": sorted(list(places))})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print('{"itinerary": []}')

if __name__ == "__main__":
    main()