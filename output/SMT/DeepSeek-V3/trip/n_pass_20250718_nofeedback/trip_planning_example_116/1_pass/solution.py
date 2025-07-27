from z3 import *

def solve_itinerary():
    # Create a solver instance
    s = Solver()

    # Cities: Split (0), Santorini (1), London (2)
    cities = {'Split': 0, 'Santorini': 1, 'London': 2}
    num_days = 18

    # Decision variables: for each day, which city are we in?
    # day_place[d] is the city on day d (1-based)
    day_place = [Int(f'day_{i}_place') for i in range(1, num_days + 1)]

    # Constraints: each day_place must be 0, 1, or 2
    for day in day_place:
        s.add(Or(day == cities['Split'], day == cities['Santorini'], day == cities['London']))

    # Flight constraints: transitions between cities must be via direct flights
    for i in range(num_days - 1):
        current = day_place[i]
        next_day = day_place[i + 1]
        # Possible transitions:
        # Split <-> London (0 <-> 2)
        # London <-> Santorini (2 <-> 1)
        s.add(Or(
            current == next_day,  # stay in the same city
            And(current == cities['Split'], next_day == cities['London']),
            And(current == cities['London'], next_day == cities['Split']),
            And(current == cities['London'], next_day == cities['Santorini']),
            And(current == cities['Santorini'], next_day == cities['London'])
        ))

    # Total days in each city
    split_days = sum([If(day == cities['Split'], 1, 0) for day in day_place])
    santorini_days = sum([If(day == cities['Santorini'], 1, 0) for day in day_place])
    london_days = sum([If(day == cities['London'], 1, 0) for day in day_place])

    s.add(split_days == 6)
    s.add(santorini_days == 7)
    s.add(london_days == 7)

    # Days 12 and 18 must be in Santorini (1-based)
    s.add(day_place[11] == cities['Santorini'])  # day 12
    s.add(day_place[17] == cities['Santorini'])  # day 18

    # Check if the problem is satisfiable
    if s.check() == sat:
        model = s.model()
        itinerary = []
        city_names = {0: 'Split', 1: 'Santorini', 2: 'London'}
        for i in range(num_days):
            day = i + 1
            city_code = model.evaluate(day_place[i]).as_long()
            city = city_names[city_code]
            itinerary.append({'day': day, 'place': city})
        return {'itinerary': itinerary}
    else:
        return {'error': 'No valid itinerary found'}

# Generate the itinerary
itinerary = solve_itinerary()
print(itinerary)