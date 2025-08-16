from z3 import *
import json

def main():
    # Define cities
    cities = ["Valencia", "Athens", "Naples", "Zurich"]

    # Create Z3 variables for the sequence of 4 cities
    c1, c2, c3, c4 = [String(f'c{i+1}') for i in range(4)]

    # Create solver
    s = Solver()

    # Ensure all cities are distinct and in the list
    s.add(Distinct(c1, c2, c3, c4))
    for city in cities:
        s.add(Or(c1 == city, c2 == city, c3 == city, c4 == city))

    # Define direct flight constraints
    def add_direct_flight(from_city, to_city):
        return And(
            Or(c1 == from_city, c2 == from_city, c3 == from_city, c4 == from_city),
            Or(c2 == to_city, c3 == to_city, c4 == to_city),
            Or(
                And(c1 == from_city, c2 == to_city),
                And(c2 == from_city, c3 == to_city),
                And(c3 == from_city, c4 == to_city)
            )
        )

    # Add all valid direct flights
    direct_flights = [
        ("Valencia", "Naples"),
        ("Valencia", "Athens"),
        ("Naples", "Valencia"),
        ("Naples", "Athens"),
        ("Athens", "Naples"),
        ("Zurich", "Naples"),
        ("Naples", "Zurich"),
        ("Athens", "Zurich"),
        ("Zurich", "Athens"),
        ("Zurich", "Valencia"),
        ("Valencia", "Zurich")
    ]

    for from_city, to_city in direct_flights:
        s.add(add_direct_flight(from_city, to_city))

    # Define durations for each segment
    a, b, c, d = Ints('a b c d')
    s.add(a >= 1, b >= 1, c >= 1, d >= 1)
    s.add(a + b + c + d == 23)

    # Map city to required duration
    required_days = {
        "Valencia": 6,
        "Athens": 6,
        "Naples": 5,
        "Zurich": 6
    }

    # Set duration based on city
    for i, city_var in enumerate([c1, c2, c3, c4]):
        for city in cities:
            s.add(If(city_var == city, locals()[chr(97 + i)] == required_days[city], True))

    # Add event constraints
    # Athens must have at least one day in [1, 6]
    s.add(Or(
        c1 == "Athens",  # starts on day 1
        And(c2 == "Athens", a <= 6),
        And(c3 == "Athens", a + b - 1 <= 6),
        And(c4 == "Athens", a + b + c - 2 <= 6)
    ))

    # Naples must have at least one day in [16, 20]
    s.add(Or(
        c4 == "Naples",  # starts on day 16
        And(c3 == "Naples", a + b - 1 >= 16),
        And(c2 == "Naples", a >= 16),
        And(c1 == "Naples", 1 >= 16)  # Impossible, but included for completeness
    ))

    # Check if the model is satisfiable
    if s.check() == sat:
        model = s.model()
        # Extract cities and durations
        cities_seq = [model[c1].as_string(), model[c2].as_string(), model[c3].as_string(), model[c4].as_string()]
        a_val = model[a].as_long()
        b_val = model[b].as_long()
        c_val = model[c].as_long()
        d_val = model[d].as_long()

        # Generate the itinerary
        itinerary = []
        current_day = 1

        for _ in range(a_val):
            itinerary.append({"day": current_day, "city": cities_seq[0]})
            current_day += 1

        for _ in range(b_val):
            itinerary.append({"day": current_day, "city": cities_seq[1]})
            current_day += 1

        for _ in range(c_val):
            itinerary.append({"day": current_day, "city": cities_seq[2]})
            current_day += 1

        for _ in range(d_val):
            itinerary.append({"day": current_day, "city": cities_seq[3]})
            current_day += 1

        # Output the JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()