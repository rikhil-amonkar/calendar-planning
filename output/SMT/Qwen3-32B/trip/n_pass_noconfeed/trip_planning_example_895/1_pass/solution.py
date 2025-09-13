from z3 import *

def main():
    cities = ['Brussels', 'Venice', 'London', 'Lisbon', 'Reykjavik', 'Santorini', 'Madrid']
    city_code = {city: idx for idx, city in enumerate(cities)}

    allowed_flights = set()
    allowed_flights.add((city_code['Venice'], city_code['Madrid']))
    allowed_flights.add((city_code['Madrid'], city_code['Venice']))
    allowed_flights.add((city_code['Lisbon'], city_code['Reykjavik']))
    allowed_flights.add((city_code['Reykjavik'], city_code['Lisbon']))
    allowed_flights.add((city_code['Brussels'], city_code['Venice']))
    allowed_flights.add((city_code['Venice'], city_code['Brussels']))
    allowed_flights.add((city_code['Venice'], city_code['Santorini']))
    allowed_flights.add((city_code['Santorini'], city_code['Venice']))
    allowed_flights.add((city_code['Lisbon'], city_code['Venice']))
    allowed_flights.add((city_code['Venice'], city_code['Lisbon']))
    allowed_flights.add((city_code['Reykjavik'], city_code['Madrid']))
    allowed_flights.add((city_code['Brussels'], city_code['London']))
    allowed_flights.add((city_code['London'], city_code['Brussels']))
    allowed_flights.add((city_code['Madrid'], city_code['London']))
    allowed_flights.add((city_code['London'], city_code['Madrid']))
    allowed_flights.add((city_code['Santorini'], city_code['London']))
    allowed_flights.add((city_code['London'], city_code['Santorini']))
    allowed_flights.add((city_code['London'], city_code['Reykjavik']))
    allowed_flights.add((city_code['Reykjavik'], city_code['London']))
    allowed_flights.add((city_code['Brussels'], city_code['Lisbon']))
    allowed_flights.add((city_code['Lisbon'], city_code['Brussels']))
    allowed_flights.add((city_code['Lisbon'], city_code['London']))
    allowed_flights.add((city_code['London'], city_code['Lisbon']))
    allowed_flights.add((city_code['Lisbon'], city_code['Madrid']))
    allowed_flights.add((city_code['Madrid'], city_code['Lisbon']))
    allowed_flights.add((city_code['Madrid'], city_code['Santorini']))
    allowed_flights.add((city_code['Santorini'], city_code['Madrid']))
    allowed_flights.add((city_code['Brussels'], city_code['Reykjavik']))
    allowed_flights.add((city_code['Reykjavik'], city_code['Brussels']))
    allowed_flights.add((city_code['Brussels'], city_code['Madrid']))
    allowed_flights.add((city_code['Madrid'], city_code['Brussels']))
    allowed_flights.add((city_code['Venice'], city_code['London']))
    allowed_flights.add((city_code['London'], city_code['Venice']))

    s = Solver()

    pos = [Int(f'pos_{i}') for i in range(1, 7)]
    s.add(And([And(1 <= pos[i], pos[i] <= 6) for i in range(6)]))
    s.add(Distinct(pos))

    sequence = [0] + pos

    for i in range(6):
        current = sequence[i]
        next_city = sequence[i + 1]
        constraints = []
        for (fr, to) in allowed_flights:
            constraints.append(And(current == fr, next_city == to))
        s.add(Or(constraints))

    start = [Int(f'start_{i}') for i in range(7)]
    end = [Int(f'end_{i}') for i in range(7)]

    durations = [2, 3, 3, 4, 3, 3, 5]

    s.add(start[0] == 1)
    s.add(end[0] == start[0] + durations[0] - 1)

    for i in range(1, 7):
        city_code_i = pos[i - 1]
        duration_i = If(city_code_i == 1, 3,
                        If(city_code_i == 2, 3,
                           If(city_code_i == 3, 4,
                              If(city_code_i == 4, 3,
                                 If(city_code_i == 5, 3,
                                    If(city_code_i == 6, 5, 0))))))
        s.add(start[i] == end[i - 1])
        s.add(end[i] == start[i] + duration_i - 1)

    s.add(end[6] == 17)

    for i in range(1, 7):
        city_code_i = sequence[i]
        s.add(Implies(city_code_i == 1, Or(
            And(start[i] <= 5, 5 <= end[i]),
            And(start[i] <= 6, 6 <= end[i]),
            And(start[i] <= 7, 7 <= end[i])
        )))

    for i in range(1, 7):
        city_code_i = sequence[i]
        s.add(Implies(city_code_i == 6, Or(
            And(start[i] <= 7, 7 <= end[i]),
            And(start[i] <= 8, 8 <= end[i]),
            And(start[i] <= 9, 9 <= end[i]),
            And(start[i] <= 10, 10 <= end[i]),
            And(start[i] <= 11, 11 <= end[i])
        )))

    if s.check() == sat:
        m = s.model()
        order = [0] + [m.evaluate(pos[i]).as_long() for i in range(6)]
        itinerary = []
        for i in range(7):
            city_code_i = order[i]
            city_name = cities[city_code_i]
            s_day = m.evaluate(start[i]).as_long()
            e_day = m.evaluate(end[i]).as_long()
            day_range = f"Day {s_day}-{e_day}"
            itinerary.append({"day_range": day_range, "place": city_name})
        import json
        print(json.dumps({"itinerary": itinerary}))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()