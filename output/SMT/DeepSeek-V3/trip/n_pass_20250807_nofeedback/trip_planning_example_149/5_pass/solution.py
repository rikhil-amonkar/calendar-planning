from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities
    London, Santorini, Istanbul = 0, 1, 2
    city_names = ['London', 'Santorini', 'Istanbul']

    # Variables for each day (0..9 for days 1..10)
    location = [Int(f'loc_{i}') for i in range(10)]
    is_transition = [Bool(f'trans_{i}') for i in range(10)]
    trans_from = [Int(f't_from_{i}') for i in range(10)]
    trans_to = [Int(f't_to_{i}') for i in range(10)]

    # Initial constraints
    for i in range(10):
        s.add(location[i] >= 0, location[i] <= 2)
        s.add(Implies(is_transition[i], 
                     And(trans_from[i] >= 0, trans_from[i] <= 2,
                         trans_to[i] >= 0, trans_to[i] <= 2,
                         trans_from[i] != trans_to[i])))
        s.add(Implies(Not(is_transition[i]), 
                     trans_from[i] == location[i],
                     trans_to[i] == location[i]))

    # Flight connections (only direct flights)
    for i in range(10):
        s.add(Implies(is_transition[i],
                     Or(
                         And(trans_from[i] == London, trans_to[i] == Istanbul),
                         And(trans_from[i] == Istanbul, trans_to[i] == London),
                         And(trans_from[i] == London, trans_to[i] == Santorini),
                         And(trans_from[i] == Santorini, trans_to[i] == London)
                     )))

    # Day-to-day consistency
    for i in range(9):
        s.add(Or(
            # Stay in same city
            And(location[i] == location[i+1], Not(is_transition[i]), Not(is_transition[i+1])),
            # Transition between cities
            And(is_transition[i], location[i] == trans_from[i], location[i+1] == trans_to[i])
        ))

    # Count days in each city (including transition days)
    def count_days(city):
        return Sum([If(Or(location[i] == city,
                       And(is_transition[i],
                           Or(trans_from[i] == city,
                              trans_to[i] == city))), 1, 0)
                   for i in range(10)])

    s.add(count_days(London) == 3)
    s.add(count_days(Santorini) == 6)
    s.add(count_days(Istanbul) == 3)

    # Conference days must be full days in Santorini
    s.add(And(location[4] == Santorini, Not(is_transition[4])))  # Day 5
    s.add(And(location[9] == Santorini, Not(is_transition[9])))  # Day 10

    # Ensure London stay is contiguous (3 consecutive days)
    london_stay = Or([And(location[i] == London,
                         location[i+1] == London,
                         location[i+2] == London,
                         Not(is_transition[i]),
                         Not(is_transition[i+1]),
                         Not(is_transition[i+2]))
                    for i in range(8)])
    s.add(london_stay)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(10):
            if is_true(model.eval(is_transition[i])):
                from_city = city_names[model.eval(trans_from[i]).as_long()]
                to_city = city_names[model.eval(trans_to[i]).as_long()]
                itinerary.append({"day": i+1, "place": f"{from_city}→{to_city}"})
            else:
                city = city_names[model.eval(location[i]).as_long()]
                itinerary.append({"day": i+1, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(itinerary)