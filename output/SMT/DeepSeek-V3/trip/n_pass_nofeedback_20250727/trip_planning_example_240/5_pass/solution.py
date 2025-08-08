from z3 import *

def solve_itinerary():
    # Create solver
    s = Solver()

    # Cities mapping
    cities = ['Prague', 'Berlin', 'Tallinn', 'Stockholm']
    city_to_int = {city: idx for idx, city in enumerate(cities)}
    int_to_city = {idx: city for idx, city in enumerate(cities)}

    # Day variables (1-12)
    days = [Int(f"day_{i}") for i in range(1, 13)]
    for day in days:
        s.add(day >= 0, day < len(cities))

    # Flight connections
    connections = {
        0: [2, 3],  # Prague connects to Tallinn and Stockholm
        1: [2, 3],   # Berlin connects to Tallinn and Stockholm
        2: [0, 1, 3], # Tallinn connects to Prague, Berlin, Stockholm
        3: [0, 1, 2]  # Stockholm connects to Prague, Berlin, Tallinn
    }

    # Flight constraints between consecutive days
    for i in range(11):
        current = days[i]
        next_day = days[i+1]
        s.add(Or(
            current == next_day,  # Stay in same city
            Or([And(current == city, next_day == neighbor) 
                for city in connections for neighbor in connections[city]])
        ))

    # City day counts
    # Prague: 2 days
    s.add(Sum([If(d == city_to_int['Prague'], 1, 0) for d in days]) == 2)
    # Berlin: 3 days including days 6 and 8
    s.add(Sum([If(d == city_to_int['Berlin'], 1, 0) for d in days]) == 3)
    s.add(days[5] == city_to_int['Berlin'])  # Day 6
    s.add(days[7] == city_to_int['Berlin'])  # Day 8
    # Tallinn: 5 days between days 8-12
    s.add(Sum([If(days[i] == city_to_int['Tallinn'], 1, 0) for i in range(7, 12)]) >= 1)
    s.add(Sum([If(d == city_to_int['Tallinn'], 1, 0) for d in days]) == 5)
    # Stockholm: 5 days
    s.add(Sum([If(d == city_to_int['Stockholm'], 1, 0) for d in days]) == 5)

    # Additional constraints to help the solver
    # Cannot be in Tallinn on day 6 or 8 (must be in Berlin)
    s.add(days[5] != city_to_int['Tallinn'])
    s.add(days[7] != city_to_int['Tallinn'])

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(12):
            day_num = i + 1
            city_idx = model.evaluate(days[i]).as_long()
            city = int_to_city[city_idx]
            itinerary.append({"day": day_num, "place": city})
        return {'itinerary': itinerary}
    else:
        return {"error": "No valid itinerary found"}

solution = solve_itinerary()
print(solution)