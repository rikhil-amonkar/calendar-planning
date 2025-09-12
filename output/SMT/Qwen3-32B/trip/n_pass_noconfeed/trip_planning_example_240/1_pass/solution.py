from z3 import *
import json

def main():
    s = Solver()

    # Define cities as 0: Prague, 1: Berlin, 2: Tallinn, 3: Stockholm
    cities = [Int(f'city_{i+1}') for i in range(12)]  # city_1 to city_12

    # Allowed direct flights between cities
    allowed_pairs = [
        (0, 2), (2, 0),  # Prague-Tallinn
        (1, 2), (2, 1),  # Berlin-Tallinn
        (2, 3), (3, 2),  # Tallinn-Stockholm
        (0, 3), (3, 0),  # Prague-Stockholm
        (3, 1), (1, 3)   # Berlin-Stockholm
    ]

    # Constraint 1: Allowed transitions between cities
    for i in range(11):  # days 1 to 11 (indices 0 to 10)
        current = cities[i]
        next_city = cities[i+1]
        allowed = Or([And(current == a, next_city == b) for a, b in allowed_pairs])
        s.add(Implies(current != next_city, allowed))

    # Constraint 2: Required durations for each city
    required_durations = {0: 2, 1: 3, 2: 5, 3: 5}
    for city_id in required_durations:
        count_in_city_vars = Sum([If(c == city_id, 1, 0) for c in cities])
        count_departures = Sum([If(And(cities[i] == city_id, cities[i] != cities[i+1]), 1, 0) for i in range(11)])
        total = count_in_city_vars + count_departures
        s.add(total == required_durations[city_id])

    # Constraint 3: Conference in Berlin on day 6 and 8
    s.add(cities[5] == 1)  # day 6 is index 5
    s.add(cities[7] == 1)  # day 8 is index 7

    # Constraint 4: Visit relatives in Tallinn between day 8 and 12
    conditions = []
    for j in range(7, 12):  # days 8 to 12 (indices 7 to 11)
        condition = Or(
            cities[j] == 2,
            And(cities[j-1] == 2, cities[j] != 2)
        )
        conditions.append(condition)
    s.add(Or(conditions))

    # Check for solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            city_val = model[cities[i]].as_long()
            itinerary.append((i + 1, city_val))  # day (1-12), city code

        # Group consecutive days into ranges
        grouped = []
        current_place = itinerary[0][1]
        start_day = 1
        for i in range(1, 12):
            day, place = itinerary[i]
            if place != current_place:
                grouped.append((start_day, i, current_place))
                current_place = place
                start_day = day
        grouped.append((start_day, 12, current_place))

        # Convert to JSON format
        city_names = {0: "Prague", 1: "Berlin", 2: "Tallinn", 3: "Stockholm"}
        result = []
        for start, end, city_code in grouped:
            result.append({
                "day_range": f"Day {start}-{end}",
                "place": city_names[city_code]
            })

        print(json.dumps({"itinerary": result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()