from z3 import *

def plan_trip(trip, flight_combinations, required_stay, max_stay, home_city):
    s = Solver()

    # Create variables for each city
    active = {city: Bool(f'active_{city}') for city in trip}
    start_vars = {city: Int(f'start_{city}') for city in trip}
    end_vars = {city: Int(f'end_{city}') for city in trip}
    stay_vars = {city: Int(f'stay_{city}') for city in trip}

    # Constraint: The first city must be active
    s.add(active[trip[0]] == True)

    # Constraints for each city
    for city in trip:
        # If active, flight times must be from the available combinations and stay time must be within [required_stay, max_stay]
        if flight_combinations[city]:
            flight_options = Or(*[And(start_vars[city] == dep, end_vars[city] == arr) for dep, arr in flight_combinations[city]])
            s.add(Implies(active[city], flight_options))
            s.add(Implies(active[city], And(stay_vars[city] >= required_stay, stay_vars[city] <= max_stay)))
        else:
            # If no flights, city must be inactive
            s.add(active[city] == False)

        # If inactive, flight times and stay time are 0
        s.add(Implies(Not(active[city]), And(start_vars[city] == 0, end_vars[city] == 0, stay_vars[city] == 0)))

    # Constraints for consecutive cities in the trip
    for i in range(len(trip) - 1):
        city1 = trip[i]
        city2 = trip[i+1]
        condition = And(active[city1], active[city2])
        consecutive_pairs = [(s1, e1, s2, e2) for (s1, e1), (s2, e2) in zip(flight_combinations[city1], flight_combinations[city2])]
        s.add(Implies(condition,
            Or([
                And(
                    start_vars[city1] == s1,
                    end_vars[city1] == e1,
                    start_vars[city2] == s2,
                    end_vars[city2] == e2
                )
                for (s1, e1, s2, e2) in consecutive_pairs
            ])
        ))

    # Constraint for returning to the starting city
    if len(trip) > 1:
        first_city = trip[0]
        last_city = trip[-1]
        condition = And(active[first_city], active[last_city])
        return_pairs = [(s1, e1, s2, e2) for (s1, e1), (s2, e2) in zip(flight_combinations[last_city], flight_combinations[first_city])]
        s.add(Implies(condition,
            Or([
                And(
                    start_vars[last_city] == s1,
                    end_vars[last_city] == e1,
                    start_vars[first_city] == s2,
                    end_vars[first_city] == e2
                )
                for (s1, e1, s2, e2) in return_pairs
            ])
        ))

    # Solve the problem
    if s.check() == sat:
        m = s.model()
        result = {}
        for city in trip:
            if is_true(m[active[city]]):
                result[city] = {
                    'flight': (m[start_vars[city]].as_long(), m[end_vars[city]].as_long()),
                    'stay': m[stay_vars[city]].as_long()
                }
            else:
                result[city] = None
        return result
    else:
        return None

# Example usage
if __name__ == "__main__":
    trip = ["New York", "London", "Paris", "New York"]
    flight_combinations = {
        "New York": [(0, 100), (200, 300)],
        "London": [(150, 250), (350, 450)],
        "Paris": [(300, 400), (500, 600)]
    }
    required_stay = 50
    max_stay = 200
    home_city = "New York"

    result = plan_trip(trip, flight_combinations, required_stay, max_stay, home_city)
    if result:
        for city, details in result.items():
            if details:
                print(f"{city}: Flight {details['flight']}, Stay {details['stay']} hours")
            else:
                print(f"{city}: Not visited")
    else:
        print("No valid trip plan found")