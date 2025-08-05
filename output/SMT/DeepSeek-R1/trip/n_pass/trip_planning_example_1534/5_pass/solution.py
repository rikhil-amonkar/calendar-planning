from z3 import *

def main():
    cities = ["Paris", "Amsterdam", "Hamburg", "Warsaw", "Vilnius", "Tallinn", "Barcelona", "Florence", "Venice", "Salzburg"]
    n_cities = len(cities)
    n_stays = 11
    total_days = 24
    travel_days = 10
    total_stay_days = total_days - travel_days  # 14 days

    # City sequence variables (11 stays)
    c = [Int(f'c_{i}') for i in range(n_stays)]
    # Stay duration variables (11 stays)
    d = [Int(f'd_{i}') for i in range(n_stays)]

    s = Solver()

    # Start and end in Paris (city 0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)

    # Durations between 1-5 days, sum to 14
    for i in range(n_stays):
        s.add(d[i] >= 1, d[i] <= 5)
    s.add(sum(d) == total_stay_days)

    # Middle 9 cities are distinct and cover cities 1-9
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] >= 1, c[i] <= 9)

    # Define bidirectional train connections
    edges = [
        (0, 1), (0, 6),  # Paris
        (1, 2),           # Amsterdam-Hamburg
        (2, 3),           # Hamburg-Warsaw
        (3, 4), (3, 8),   # Warsaw
        (4, 5),           # Vilnius-Tallinn
        (7, 8),           # Florence-Venice
        (8, 9),           # Venice-Salzburg
        (6, 7)            # Barcelona-Florence (ADDED)
    ]
    # Make bidirectional
    allowed_edges = []
    for u, v in edges:
        allowed_edges.append((u, v))
        allowed_edges.append((v, u))

    # Consecutive cities must be connected
    for i in range(n_stays - 1):
        s.add(Or([And(c[i] == u, c[i+1] == v) for u, v in allowed_edges]))

    if s.check() == sat:
        model = s.model()
        city_seq = [model.evaluate(c[i]).as_long() for i in range(n_stays)]
        dur_seq = [model.evaluate(d[i]).as_long() for i in range(n_stays)]
        
        # Build itinerary
        itinerary = []
        day = 1
        for i in range(n_stays):
            stay_days = dur_seq[i]
            end_day = day + stay_days - 1
            if stay_days == 1:
                day_str = f"Day {day}"
            else:
                day_str = f"Day {day}-{end_day}"
            itinerary.append({
                "day_range": day_str,
                "place": cities[city_seq[i]]
            })
            day = end_day + 2  # Next stay after travel day
        
        print({"itinerary": itinerary})
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()