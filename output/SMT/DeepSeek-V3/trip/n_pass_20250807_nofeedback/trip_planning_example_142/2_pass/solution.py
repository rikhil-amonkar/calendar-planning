from z3 import *

def solve_itinerary():
    s = Solver()

    days = range(1, 8)  # Days 1 to 7
    n_days = len(days)

    # Cities
    Madrid, Dublin, Tallinn = 0, 1, 2
    city_names = {Madrid: 'Madrid', Dublin: 'Dublin', Tallinn: 'Tallinn'}

    # Variables: city each day
    day_city = [Int(f'day_{day}_city') for day in days]

    # Each day's city is one of the three
    for dc in day_city:
        s.add(Or(dc == Madrid, dc == Dublin, dc == Tallinn))

    # Workshop in Tallinn on days 6 and 7
    s.add(day_city[5] == Tallinn)  # day 6
    s.add(day_city[6] == Tallinn)  # day 7

    # Flight transitions: only direct flights
    flight_days = []
    for i in range(n_days - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        s.add(Or(
            current == next_c,  # same city
            And(current == Madrid, next_c == Dublin),
            And(current == Dublin, next_c == Madrid),
            And(current == Dublin, next_c == Tallinn),
            And(current == Tallinn, next_c == Dublin)
        ))
        # Track whether this is a flight day
        flight_day = If(current != next_c, 1, 0)
        flight_days.append(flight_day)

    total_flight_days = Sum(flight_days)

    # Number of days per city (including flight days)
    madrid_days = Sum([If(day_city[i] == Madrid, 1, 0) for i in range(n_days)])
    dublin_days = Sum([If(day_city[i] == Dublin, 1, 0) for i in range(n_days)])
    tallinn_days = Sum([If(day_city[i] == Tallinn, 1, 0) for i in range(n_days)])

    s.add(madrid_days == 4)
    s.add(dublin_days == 3)
    s.add(tallinn_days == 2)

    # The number of flight days must be 2 (since 4 + 3 + 2 = 9, and 7 + 2 = 9)
    s.add(total_flight_days == 2)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for day in days:
            city_val = model.evaluate(day_city[day - 1])
            city_code = city_val.as_long()
            itinerary.append({'day': day, 'place': city_names[city_code]})

        output = {'itinerary': itinerary}
        return output
    else:
        return None

solution = solve_itinerary()
if solution:
    import json
    print(json.dumps(solution, indent=2))
else:
    print("No solution found.")