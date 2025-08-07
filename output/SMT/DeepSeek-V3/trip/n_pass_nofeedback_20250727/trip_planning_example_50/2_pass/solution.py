from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Days are 1 to 12
    days = 12
    cities = ['Vilnius', 'Munich', 'Mykonos']
    city_codes = {c: i for i, c in enumerate(cities)}
    Vilnius, Munich, Mykonos = city_codes['Vilnius'], city_codes['Munich'], city_codes['Mykonos']

    # Variables: for each day, which city are you in?
    day_city = [Int(f'day_{i}_city') for i in range(1, days + 1)]

    # Constraints: each day's city must be 0, 1, or 2
    for dc in day_city:
        s.add(Or(dc == Vilnius, dc == Munich, dc == Mykonos))

    # Flight constraints: transitions between cities must be via direct flights
    # Direct flights: Vilnius <-> Munich, Munich <-> Mykonos
    for i in range(days - 1):
        current = day_city[i]
        next_ = day_city[i + 1]
        # Possible transitions:
        # same city, or direct flights
        s.add(Or(
            current == next_,  # stay in the same city
            And(current == Vilnius, next_ == Munich),  # V -> M
            And(current == Munich, next_ == Vilnius),   # M -> V
            And(current == Munich, next_ == Mykonos),   # M -> My
            And(current == Mykonos, next_ == Munich)    # My -> M
        ))

    # Total days per city
    total_vilnius = sum([If(day_city[i] == Vilnius, 1, 0) for i in range(days)])
    total_munich = sum([If(day_city[i] == Munich, 1, 0) for i in range(days)])
    total_mykonos = sum([If(day_city[i] == Mykonos, 1, 0) for i in range(days)])

    s.add(total_vilnius == 4)
    s.add(total_munich == 3)
    s.add(total_mykonos == 7)

    # Check if the solver can find a solution
    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(days):
            city_code = model.evaluate(day_city[i]).as_long()
            city = cities[city_code]
            itinerary.append({"day": i + 1, "place": city})
        
        # Verify the counts
        vilnius_days = sum(1 for entry in itinerary if entry['place'] == 'Vilnius')
        munich_days = sum(1 for entry in itinerary if entry['place'] == 'Munich')
        mykonos_days = sum(1 for entry in itinerary if entry['place'] == 'Mykonos')
        assert vilnius_days == 4 and munich_days == 3 and mykonos_days == 7

        # Verify transitions
        for i in range(days - 1):
            current = itinerary[i]['place']
            next_place = itinerary[i+1]['place']
            if current != next_place:
                assert (current == 'Vilnius' and next_place == 'Munich') or \
                       (current == 'Munich' and next_place == 'Vilnius') or \
                       (current == 'Munich' and next_place == 'Mykonos') or \
                       (current == 'Mykonos' and next_place == 'Munich'), \
                       f"Invalid transition from {current} to {next_place}"

        return {'itinerary': itinerary}
    else:
        return None

result = solve_itinerary()
if result:
    import json
    print(json.dumps(result, indent=2))
else:
    print("No solution found.")