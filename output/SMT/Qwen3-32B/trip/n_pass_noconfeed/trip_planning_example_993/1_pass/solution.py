from z3 import *
import json

def main():
    # Define cities and their durations
    # 0: Riga (2 days)
    # 1: Frankfurt (3)
    # 2: Amsterdam (2)
    # 3: Vilnius (5)
    # 4: London (2)
    # 5: Stockholm (3)
    # 6: Bucharest (4)
    durations = [2, 3, 2, 5, 2, 3, 4]

    # Direct flight pairs (city_a, city_b)
    allowed_pairs = [
        (4, 2), (2, 4),  # London-Amsterdam
        (3, 1), (1, 3),  # Vilnius-Frankfurt
        (0, 3), (3, 0),  # Riga-Vilnius
        (0, 5), (5, 0),  # Riga-Stockholm
        (4, 6), (6, 4),  # London-Bucharest
        (2, 5), (5, 2),  # Amsterdam-Stockholm
        (2, 1), (1, 2),  # Amsterdam-Frankfurt
        (1, 5), (5, 1),  # Frankfurt-Stockholm
        (6, 0), (0, 6),  # Bucharest-Riga
        (2, 0), (0, 2),  # Amsterdam-Riga
        (2, 6), (6, 2),  # Amsterdam-Bucharest
        (0, 1), (1, 0),  # Riga-Frankfurt
        (6, 1), (1, 6),  # Bucharest-Frankfurt
        (4, 1), (1, 4),  # London-Frankfurt
        (4, 5), (5, 4),  # London-Stockholm
        (2, 3), (3, 2),  # Amsterdam-Vilnius
    ]

    # Create Z3 solver
    s = Solver()

    # Variables for the sequence of cities (positions 0-6)
    cities = [Int(f'city_{i}') for i in range(7)]

    # Variables for start and end days of each city
    start_day = [Int(f'start_day_{i}') for i in range(7)]
    end_day = [Int(f'end_day_{i}') for i in range(7)]

    # Constraints for cities to be unique and in range
    s.add(Distinct(cities))
    for c in cities:
        s.add(And(0 <= c, c <= 6))

    # Constraints for end_day = start_day + duration - 1
    for i in range(7):
        s.add(end_day[i] == start_day[i] + durations[i] - 1)

    # Fixed constraints for Vilnius (3), Stockholm (5), Amsterdam (2)
    s.add(start_day[3] == 7)
    s.add(end_day[3] == 11)
    s.add(start_day[5] == 13)
    s.add(end_day[5] == 15)
    s.add(start_day[2] == 2)
    s.add(end_day[2] == 3)

    # Constraints for consecutive cities in the sequence
    for i in range(6):  # i from 0 to 5
        # end_day of current city == start_day of next city
        current_city = cities[i]
        next_city = cities[i+1]
        s.add(end_day[current_city] == start_day[next_city])

        # Direct flight between current and next city
        allowed = []
        for a, b in allowed_pairs:
            allowed.append(And(current_city == a, next_city == b))
        s.add(Or(allowed))

    # Check if the constraints are satisfiable
    if s.check() == sat:
        model = s.model()

        # Extract the cities sequence
        cities_sequence = [model.evaluate(c).as_long() for c in cities]

        # Extract start_day and end_day for each city in the sequence
        itinerary = []
        for city_idx in cities_sequence:
            sd = model.evaluate(start_day[city_idx]).as_long()
            ed = model.evaluate(end_day[city_idx]).as_long()
            city_name = None
            if city_idx == 0:
                city_name = "Riga"
            elif city_idx == 1:
                city_name = "Frankfurt"
            elif city_idx == 2:
                city_name = "Amsterdam"
            elif city_idx == 3:
                city_name = "Vilnius"
            elif city_idx == 4:
                city_name = "London"
            elif city_idx == 5:
                city_name = "Stockholm"
            elif city_idx == 6:
                city_name = "Bucharest"
            itinerary.append({
                "day_range": f"Day {sd}-{ed}",
                "place": city_name
            })

        # Output the JSON
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()