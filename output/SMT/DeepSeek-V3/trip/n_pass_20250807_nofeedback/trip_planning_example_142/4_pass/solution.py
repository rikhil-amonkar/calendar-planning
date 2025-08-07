from z3 import *

def solve_itinerary():
    s = Solver()

    # Days 1 through 7
    days = range(1, 8)
    n_days = len(days)

    # Cities
    Madrid, Dublin, Tallinn = 0, 1, 2
    city_names = {Madrid: 'Madrid', Dublin: 'Dublin', Tallinn: 'Tallinn'}

    # Variables for each day's city
    day_city = [Int(f'day_{day}_city') for day in days]

    # Each day must be in one of the three cities
    for dc in day_city:
        s.add(Or(dc == Madrid, dc == Dublin, dc == Tallinn))

    # Workshop constraint: must be in Tallinn on days 6 and 7
    s.add(day_city[5] == Tallinn)  # day 6
    s.add(day_city[6] == Tallinn)  # day 7

    # Flight transitions - only direct flights allowed
    for i in range(n_days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        s.add(Or(
            current == next_c,  # stay in same city
            And(current == Madrid, next_c == Dublin),
            And(current == Dublin, next_c == Madrid),
            And(current == Dublin, next_c == Tallinn),
            And(current == Tallinn, next_c == Dublin)
        ))

    # Count days in each city (including flight days)
    madrid_days = Sum([If(day_city[i] == Madrid, 1, 0) for i in range(n_days)])
    dublin_days = Sum([If(day_city[i] == Dublin, 1, 0) for i in range(n_days)])
    tallinn_days = Sum([If(day_city[i] == Tallinn, 1, 0) for i in range(n_days)])

    # Required days in each city
    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)

    # Count flight days (when city changes)
    flight_days = Sum([If(day_city[i] != day_city[i+1], 1, 0) for i in range(n_days-1)])
    s.add(flight_days == 2)  # Exactly 2 flight days needed

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in days:
            city_val = model.evaluate(day_city[day-1])
            city_code = city_val.as_long()
            itinerary.append({'day': day, 'place': city_names[city_code]})

        # Verify the solution
        madrid_count = sum(1 for x in itinerary if x['place'] == 'Madrid')
        dublin_count = sum(1 for x in itinerary if x['place'] == 'Dublin')
        tallinn_count = sum(1 for x in itinerary if x['place'] == 'Tallinn')
        flight_count = sum(1 for i in range(len(itinerary)-1) 
                       if itinerary[i]['place'] != itinerary[i+1]['place'])

        assert madrid_count == 4
        assert dublin_count == 3
        assert tallinn_count == 2
        assert flight_count == 2
        assert itinerary[5]['place'] == 'Tallinn'
        assert itinerary[6]['place'] == 'Tallinn'

        return {'itinerary': itinerary}
    else:
        return None

solution = solve_itinerary()
if solution:
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")