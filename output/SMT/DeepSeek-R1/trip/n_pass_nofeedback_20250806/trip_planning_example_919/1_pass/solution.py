import z3
import json

def main():
    # Define the city enum
    city_names = ['Vienna', 'Milan', 'Rome', 'Riga', 'Lisbon', 'Vilnius', 'Oslo']
    CitySort, cities = z3.EnumSort('City', city_names)
    Vienna, Milan, Rome, Riga, Lisbon, Vilnius, Oslo = cities

    # Create a mapping from name to constant
    city_dict = {name: const for name, const in zip(city_names, cities)}

    # Define the flight connections
    bidirectional_pairs = [
        ('Riga', 'Oslo'),
        ('Rome', 'Oslo'),
        ('Vienna', 'Milan'),
        ('Vienna', 'Vilnius'),
        ('Vienna', 'Lisbon'),
        ('Riga', 'Milan'),
        ('Lisbon', 'Oslo'),
        ('Rome', 'Lisbon'),
        ('Vienna', 'Riga'),
        ('Vienna', 'Rome'),
        ('Milan', 'Oslo'),
        ('Vienna', 'Oslo'),
        ('Vilnius', 'Oslo'),
        ('Vilnius', 'Milan'),
        ('Riga', 'Lisbon'),
        ('Milan', 'Lisbon')
    ]
    unidirectional = [
        ('Rome', 'Riga'),
        ('Riga', 'Vilnius')
    ]

    allowed_flights = []
    for a, b in bidirectional_pairs:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_flights.append((a_const, b_const))
        allowed_flights.append((b_const, a_const))
    for a, b in unidirectional:
        a_const = city_dict[a]
        b_const = city_dict[b]
        allowed_flights.append((a_const, b_const))

    # Define variables for the trip
    city_vars = [z3.Const(f'city_{i}', CitySort) for i in range(15)]
    fly_vars = [z3.Bool(f'fly_{i}') for i in range(14)]

    solver = z3.Solver()

    # Start in Vienna on day 1
    solver.add(city_vars[0] == Vienna)

    # Flight and city transition constraints
    for i in range(14):
        solver.add(z3.Implies(fly_vars[i], city_vars[i] != city_vars[i+1]))
        solver.add(z3.Implies(z3.Not(fly_vars[i]), city_vars[i] == city_vars[i+1]))
        flight_ok = z3.Or([z3.And(city_vars[i] == a, city_vars[i+1] == b) for (a, b) in allowed_flights])
        solver.add(z3.Implies(fly_vars[i], flight_ok))

    # Total flights must be 6
    solver.add(z3.Sum([z3.If(fly, 1, 0) for fly in fly_vars]) == 6)

    # Total days per city
    total_days = {}
    for c in cities:
        count = 0
        for i in range(15):
            count += z3.If(city_vars[i] == c, 1, 0)
        for i in range(14):
            count += z3.If(z3.And(fly_vars[i], city_vars[i+1] == c), 1, 0)
        total_days[c] = count

    # Add duration constraints
    solver.add(total_days[Vienna] == 4)
    solver.add(total_days[Milan] == 2)
    solver.add(total_days[Rome] == 3)
    solver.add(total_days[Riga] == 2)
    solver.add(total_days[Lisbon] == 3)
    solver.add(total_days[Vilnius] == 4)
    solver.add(total_days[Oslo] == 3)

    # Specific day constraints
    solver.add(z3.Or(city_vars[3] == Vienna, z3.And(fly_vars[3], city_vars[4] == Vienna)))  # Day 4 in Vienna
    lisbon_cond = z3.Or(
        city_vars[10] == Lisbon,
        z3.And(fly_vars[10], city_vars[11] == Lisbon),
        city_vars[11] == Lisbon,
        z3.And(fly_vars[11], city_vars[12] == Lisbon),
        city_vars[12] == Lisbon,
        z3.And(fly_vars[12], city_vars[13] == Lisbon)
    )
    solver.add(lisbon_cond)  # Lisbon between days 11-13
    oslo_cond = z3.Or(
        city_vars[12] == Oslo,
        z3.And(fly_vars[12], city_vars[13] == Oslo),
        city_vars[13] == Oslo,
        z3.And(fly_vars[13], city_vars[14] == Oslo),
        city_vars[14] == Oslo
    )
    solver.add(oslo_cond)  # Oslo between days 13-15

    # Solve and output
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for day_index in range(15):
            day_number = day_index + 1
            start_city = model[city_vars[day_index]]
            start_name = None
            for idx, c in enumerate(cities):
                if z3.is_true(model.eval(start_city == c)):
                    start_name = city_names[idx]
            if day_index < 14 and z3.is_true(model.eval(fly_vars[day_index])):
                end_city = model[city_vars[day_index+1]]
                end_name = None
                for idx, c in enumerate(cities):
                    if z3.is_true(model.eval(end_city == c)):
                        end_name = city_names[idx]
                places = [start_name, end_name]
            else:
                places = [start_name]
            itinerary.append({"day": day_number, "place": places})
        print(json.dumps({"itinerary": itinerary}))
    else:
        print('{"itinerary": []}')

if __name__ == '__main__':
    main()