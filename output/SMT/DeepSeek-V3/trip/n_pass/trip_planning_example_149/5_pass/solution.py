from z3 import *
import json

def solve_itinerary():
    # Cities mapping
    cities = ['London', 'Santorini', 'Istanbul']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}

    # Days 1-10
    days = 10
    day_numbers = range(1, days + 1)

    # Create Z3 variables for each day's city
    assignments = [Int(f'day_{i}') for i in day_numbers]

    solver = Solver()

    # Each day must be assigned to a valid city
    for day in assignments:
        solver.add(day >= 0, day <= 2)

    # Flight constraints - can only transition between connected cities
    for i in range(days - 1):
        current = assignments[i]
        next_day = assignments[i + 1]
        solver.add(Implies(current != next_day,
                          Or(
                              And(current == city_to_int['London'], next_day == city_to_int['Istanbul']),
                              And(current == city_to_int['Istanbul'], next_day == city_to_int['London']),
                              And(current == city_to_int['London'], next_day == city_to_int['Santorini']),
                              And(current == city_to_int['Santorini'], next_day == city_to_int['London'])
                          )))

    # Total days constraints
    # London: 3 days (including flight days)
    solver.add(Sum([If(assignments[i] == city_to_int['London'], 1, 0) for i in range(days)]) == 3)
    # Santorini: 6 days (including flight days and conference days)
    solver.add(Sum([If(assignments[i] == city_to_int['Santorini'], 1, 0) for i in range(days)]) == 6)
    # Conference days in Santorini
    solver.add(assignments[4] == city_to_int['Santorini'])  # Day 5
    solver.add(assignments[9] == city_to_int['Santorini'])  # Day 10
    # Istanbul: 3 days (including flight days)
    solver.add(Sum([If(assignments[i] == city_to_int['Istanbul'], 1, 0) for i in range(days)]) == 3)

    # Find solution
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(days):
            day_num = i + 1
            city_idx = model.evaluate(assignments[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({'day': day_num, 'place': city})
        
        # Verify the solution meets all constraints
        london_days = sum(1 for entry in itinerary if entry['place'] == 'London')
        santorini_days = sum(1 for entry in itinerary if entry['place'] == 'Santorini')
        istanbul_days = sum(1 for entry in itinerary if entry['place'] == 'Istanbul')
        
        assert london_days == 3, "London days constraint not met"
        assert santorini_days == 6, "Santorini days constraint not met"
        assert istanbul_days == 3, "Istanbul days constraint not met"
        assert itinerary[4]['place'] == 'Santorini', "Day 5 conference constraint not met"
        assert itinerary[9]['place'] == 'Santorini', "Day 10 conference constraint not met"

        # Check flight transitions
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i + 1]['place']
            if current != next_place:
                assert (current == 'London' and next_place == 'Istanbul') or \
                       (current == 'Istanbul' and next_place == 'London') or \
                       (current == 'London' and next_place == 'Santorini') or \
                       (current == 'Santorini' and next_place == 'London'), \
                       f"Invalid flight from {current} to {next_place} on day {i+1}"

        return json.dumps({'itinerary': itinerary}, indent=2)
    else:
        return json.dumps({'error': 'No valid itinerary found'}, indent=2)

print(solve_itinerary())