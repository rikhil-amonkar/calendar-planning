from z3 import *

def main():
    # Cities: Dublin, Helsinki, Riga, Reykjavik, Vienna, Tallinn
    cities = ["Dublin", "Helsinki", "Riga", "Reykjavik", "Vienna", "Tallinn"]
    n_cities = len(cities)
    n_days = 15
    n_travel_days = 14  # days 1 to 14

    # Define the edges for direct flights (bidirectional)
    edges = set()
    edges.add((0, 1))  # Dublin - Helsinki
    edges.add((0, 2))  # Dublin - Riga
    edges.add((0, 3))  # Dublin - Reykjavik
    edges.add((0, 4))  # Dublin - Vienna
    edges.add((0, 5))  # Dublin - Tallinn
    edges.add((1, 2))  # Helsinki - Riga
    edges.add((1, 3))  # Helsinki - Reykjavik
    edges.add((1, 4))  # Helsinki - Vienna
    edges.add((1, 5))  # Helsinki - Tallinn
    edges.add((2, 4))  # Riga - Vienna
    edges.add((2, 5))  # Riga - Tallinn
    edges.add((3, 4))  # Reykjavik - Vienna

    # Create directed edges (both directions)
    directed_edges = []
    for (a, b) in edges:
        directed_edges.append((a, b))
        directed_edges.append((b, a))

    # Required days per city: [Dublin, Helsinki, Riga, Reykjavik, Vienna, Tallinn]
    required_days = [5, 3, 3, 2, 2, 5]

    # Create Z3 variables
    base_city = [Int('base_city_%d' % d) for d in range(1, n_days+1)]  # base_city[0] to base_city[14] for days 1 to 15
    travel = [Bool('travel_%d' % d) for d in range(1, n_travel_days+1)]  # travel[0] to travel[13] for days 1 to 14

    s = Solver()

    # Constraint: base_city values must be between 0 and 5
    for i in range(n_days):
        s.add(base_city[i] >= 0, base_city[i] < n_cities)

    # Constraints for travel and base_city changes
    for d in range(n_travel_days):
        # If we travel on day d+1, then (base_city[d], base_city[d+1]) must be in directed_edges
        edge_options = []
        for (a, b) in directed_edges:
            edge_options.append(And(base_city[d] == a, base_city[d+1] == b))
        s.add(Implies(travel[d], Or(edge_options)))
        # If we do not travel, then base_city[d] must equal base_city[d+1]
        s.add(Implies(Not(travel[d]), base_city[d] == base_city[d+1]))

    # Total days per city
    total_days = [0] * n_cities
    for c in range(n_cities):
        # Count days where we start in city c
        count_start = Sum([If(base_city[d] == c, 1, 0) for d in range(n_days)])
        # Count travel days where we arrive in city c (on travel day d, we arrive in base_city[d+1])
        count_arrive = Sum([If(And(travel[d], base_city[d+1] == c), 1, 0) for d in range(n_travel_days)])
        total_days[c] = count_start + count_arrive
        s.add(total_days[c] == required_days[c])

    # Special constraints for events
    # Helsinki: must be present on at least one day between day 3 and 5 (inclusive)
    helsinki_days = []
    # Day 3: index 2 in base_city (base_city[2] is the start of day3), and travel[2] is travel on day3 (if any)
    helsinki_days.append(base_city[2] == 1)  # day3: start in Helsinki
    helsinki_days.append(And(travel[2], base_city[3] == 1))  # day3: travel to Helsinki on day3
    helsinki_days.append(base_city[3] == 1)  # day4: start in Helsinki
    helsinki_days.append(And(travel[3], base_city[4] == 1))  # day4: travel to Helsinki on day4
    helsinki_days.append(base_city[4] == 1)  # day5: start in Helsinki
    helsinki_days.append(And(travel[4], base_city[5] == 1))  # day5: travel to Helsinki on day5
    s.add(Or(helsinki_days))

    # Vienna: must be present on at least one day between day 2 and 3 (inclusive)
    vienna_days = []
    # Day2: base_city[1] and travel[1] (if travel on day2)
    vienna_days.append(base_city[1] == 4)  # day2: start in Vienna
    vienna_days.append(And(travel[1], base_city[2] == 4))  # day2: travel to Vienna on day2
    vienna_days.append(base_city[2] == 4)  # day3: start in Vienna
    vienna_days.append(And(travel[2], base_city[3] == 4))  # day3: travel to Vienna on day3
    s.add(Or(vienna_days))

    # Tallinn: must be present on at least one day between day 7 and 11 (inclusive)
    tallinn_days = []
    # Days: 7 to 11 -> base_city indices: day7: index6, day8:7, day9:8, day10:9, day11:10
    for d in range(6, 11):  # d from 6 to 10 (for base_city indices for day7 to day11 starts)
        # For day (d+1): base_city[d] is the start, and travel[d] is the travel on that day (if d < 14, which it is: d from 6 to 10)
        tallinn_days.append(base_city[d] == 5)
        if d < n_travel_days:  # d from 6 to 10, and n_travel_days=14, so d<14 -> always true for d<=10
            tallinn_days.append(And(travel[d], base_city[d+1] == 5))
    s.add(Or(tallinn_days))

    # Exactly 5 travel days
    travel_count = Sum([If(travel[d], 1, 0) for d in range(n_travel_days)])
    s.add(travel_count == 5)

    # Check and print the model
    if s.check() == sat:
        m = s.model()
        # Get the base_city values
        base_city_vals = [m.evaluate(base_city[i]).as_long() for i in range(n_days)]
        travel_vals = [m.evaluate(travel[d]) for d in range(n_travel_days)]

        # Print the schedule
        print("Day\tCities")
        for day in range(1, n_days+1):
            idx = day - 1
            cities_today = set()
            cities_today.add(base_city_vals[idx])
            if day <= n_travel_days:
                if travel_vals[idx]:
                    cities_today.add(base_city_vals[idx+1])
            # Convert indices to city names
            city_names = [cities[c] for c in cities_today]
            print(f"{day}\t{', '.join(city_names)}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()