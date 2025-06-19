from z3 import *
import json

def main():
    cities = ["Prague", "Stuttgart", "Split", "Krakow", "Florence"]
    n_days = 8
    start_city = [Int(f'start_{i}') for i in range(n_days)]
    end_city = [Int(f'end_{i}') for i in range(n_days)]

    s = Solver()

    for i in range(n_days):
        s.add(start_city[i] >= 0)
        s.add(start_city[i] < 5)
        s.add(end_city[i] >= 0)
        s.add(end_city[i] < 5)

    for i in range(n_days - 1):
        s.add(end_city[i] == start_city[i + 1])

    s.add(end_city[1] == 1)
    s.add(start_city[2] == 1)
    s.add(end_city[2] == 2)

    allowed_pairs = [
        (1, 2), (2, 1),
        (0, 4), (4, 0),
        (3, 1), (1, 3),
        (3, 2), (2, 3),
        (2, 0), (0, 2),
        (3, 0), (0, 3)
    ]
    for i in range(n_days):
        flight_day = Or([And(start_city[i] == a, end_city[i] == b) for (a, b) in allowed_pairs])
        s.add(If(start_city[i] != end_city[i], flight_day, True))

    city_days = [4, 2, 2, 2, 2]
    for c, req_days in enumerate(city_days):
        total = 0
        for i in range(n_days):
            total += If(Or(start_city[i] == c, end_city[i] == c), 1, 0)
        s.add(total == req_days)

    if s.check() == sat:
        m = s.model()
        start_vals = [m.eval(start_city[i]).as_long() for i in range(n_days)]
        end_vals = [m.eval(end_city[i]).as_long() for i in range(n_days)]

        blocks = []
        current_city = start_vals[0]
        start_day = 0
        for i in range(n_days):
            if start_vals[i] != current_city:
                current_city = start_vals[i]
            if start_vals[i] != end_vals[i]:
                blocks.append((start_day, i, current_city))
                current_city = end_vals[i]
                start_day = i
        blocks.append((start_day, n_days - 1, current_city))

        itinerary = []
        for s_day, e_day, c in blocks:
            city_name = cities[c]
            if s_day == e_day:
                day_range_str = f"Day {s_day + 1}"
            else:
                day_range_str = f"Day {s_day + 1}-{e_day + 1}"
            itinerary.append({"day_range": day_range_str, "place": city_name})

        for i in range(n_days):
            if start_vals[i] != end_vals[i]:
                dep_city = cities[start_vals[i]]
                arr_city = cities[end_vals[i]]
                day_str = f"Day {i + 1}"
                itinerary.append({"day_range": day_str, "place": dep_city})
                itinerary.append({"day_range": day_str, "place": arr_city})

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()