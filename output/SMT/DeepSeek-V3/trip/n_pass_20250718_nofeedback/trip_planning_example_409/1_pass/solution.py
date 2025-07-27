from z3 import *

def solve_itinerary():
    # Cities and their required days
    cities = {
        'Zurich': 3,
        'Helsinki': 2,
        'Hamburg': 2,
        'Bucharest': 2,
        'Split': 7
    }
    city_list = list(cities.keys())
    num_days = 12

    # Direct flights adjacency list
    direct_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Helsinki', 'Bucharest', 'Zurich', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }

    # Correcting the adjacency list for typos (Helsinki vs Helsinki, etc.)
    corrected_flights = {
        'Zurich': ['Helsinki', 'Hamburg', 'Bucharest', 'Split'],
        'Helsinki': ['Zurich', 'Hamburg', 'Split'],
        'Hamburg': ['Helsinki', 'Bucharest', 'Zurich', 'Split'],
        'Bucharest': ['Hamburg', 'Zurich'],
        'Split': ['Zurich', 'Helsinki', 'Hamburg']
    }

    # Create a Z3 solver instance
    s = Solver()

    # Create variables: day[i] is the city visited on day i+1 (days are 1-based)
    day = [Int(f'day_{i}') for i in range(num_days)]
    
    # Map each city to an integer
    city_to_int = {city: idx for idx, city in enumerate(city_list)}
    int_to_city = {idx: city for idx, city in enumerate(city_list)}

    # Add constraints: each day's variable must be one of the city indices
    for d in day:
        s.add(Or([d == city_to_int[city] for city in city_list]))

    # Constraint: Zurich must be visited for 3 days, including at least one day between 1 and 3 (0-based: days 0, 1, or 2)
    zurich_days = [If(day[i] == city_to_int['Zurich'], 1, 0) for i in range(3)]
    s.add(Sum(zurich_days) >= 1)  # At least one of the first three days is Zurich

    total_zurich = Sum([If(day[i] == city_to_int['Zurich'], 1, 0) for i in range(num_days)])
    s.add(total_zurich == 3)

    # Split must be visited for 7 days, including days 4 and 10 (1-based: days 3 and 9 in 0-based)
    s.add(day[3] == city_to_int['Split'])  # Day 4 (0-based 3)
    s.add(day[9] == city_to_int['Split'])  # Day 10 (0-based 9)

    total_split = Sum([If(day[i] == city_to_int['Split'], 1, 0) for i in range(num_days)])
    s.add(total_split == 7)

    # Other cities' day counts
    total_helsinki = Sum([If(day[i] == city_to_int['Helsinki'], 1, 0) for i in range(num_days)])
    s.add(total_helsinki == 2)

    total_hamburg = Sum([If(day[i] == city_to_int['Hamburg'], 1, 0) for i in range(num_days)])
    s.add(total_hamburg == 2)

    total_bucharest = Sum([If(day[i] == city_to_int['Bucharest'], 1, 0) for i in range(num_days)])
    s.add(total_bucharest == 2)

    # Flight constraints: consecutive days must be either the same city or connected by a direct flight
    for i in range(num_days - 1):
        current_city = day[i]
        next_city = day[i+1]
        # Either same city or connected
        s.add(Or(
            current_city == next_city,
            *[
                And(current_city == city_to_int[city_a], next_city == city_to_int[city_b])
                for city_a in corrected_flights
                for city_b in corrected_flights[city_a]
            ]
        ))

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(num_days):
            city_idx = model.evaluate(day[i]).as_long()
            itinerary.append({"day": i+1, "place": int_to_city[city_idx]})
        
        # Verify the counts
        counts = {city: 0 for city in city_list}
        for entry in itinerary:
            counts[entry['place']] += 1
        assert counts['Zurich'] == 3
        assert counts['Split'] == 7
        assert counts['Helsinki'] == 2
        assert counts['Hamburg'] == 2
        assert counts['Bucharest'] == 2
        
        # Verify the Zurich wedding days (at least one day between 1-3)
        zurich_in_first_three = sum(1 for entry in itinerary[:3] if entry['place'] == 'Zurich')
        assert zurich_in_first_three >= 1
        
        # Verify Split conference days (days 4 and 10)
        assert itinerary[3]['place'] == 'Split'
        assert itinerary[9]['place'] == 'Split'
        
        # Verify flight connections
        for i in range(num_days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert next_place in corrected_flights[current], f"No flight from {current} to {next_place} on day {i+1}"
        
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the function and print the result
result = solve_itinerary()
import json
print(json.dumps(result, indent=2))