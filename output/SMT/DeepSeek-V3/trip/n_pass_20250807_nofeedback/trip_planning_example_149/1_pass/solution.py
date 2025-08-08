from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities
    London, Santorini, Istanbul = 0, 1, 2
    city_names = ['London', 'Santorini', 'Istanbul']

    # Variables for each day (0..9 for days 1..10)
    arrival = [Int(f'arrival_{i}') for i in range(10)]
    departure = [Int(f'departure_{i}') for i in range(10)]

    # Initial constraints: arrival and departure must be valid cities
    for i in range(10):
        s.add(And(arrival[i] >= 0, arrival[i] <= 2))
        s.add(And(departure[i] >= 0, departure[i] <= 2))

    # Consistency between days: departure of day i is arrival of day i+1
    for i in range(9):
        s.add(departure[i] == arrival[i+1])

    # Flight constraints: transitions can only be between connected cities
    for i in range(10):
        s.add(Or(
            arrival[i] == departure[i],  # same city
            And(arrival[i] == London, departure[i] == Istanbul),
            And(arrival[i] == Istanbul, departure[i] == London),
            And(arrival[i] == London, departure[i] == Santorini),
            And(arrival[i] == Santorini, departure[i] == London)
        ))

    # Total days per city (count arrival or departure)
    total_london = Sum([If(Or(arrival[i] == London, departure[i] == London), 1, 0) for i in range(10)])
    total_santorini = Sum([If(Or(arrival[i] == Santorini, departure[i] == Santorini), 1, 0) for i in range(10)])
    total_istanbul = Sum([If(Or(arrival[i] == Istanbul, departure[i] == Istanbul), 1, 0) for i in range(10)])

    s.add(total_london == 3)
    s.add(total_santorini == 6)
    s.add(total_istanbul == 3)

    # Conference days: day 4 and day 9 (0-based) must be in Santorini
    s.add(arrival[4] == Santorini)  # Day 5
    s.add(arrival[9] == Santorini)  # Day 10

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(10):
            arr = model.evaluate(arrival[i]).as_long()
            place = city_names[arr]
            itinerary.append({"day": i+1, "place": place})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

# Execute the solver
itinerary = solve_itinerary()
print(itinerary)