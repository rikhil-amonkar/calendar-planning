from z3 import *

def solve_itinerary():
    s = Solver()

    # Cities
    London, Santorini, Istanbul = 0, 1, 2
    city_names = ['London', 'Santorini', 'Istanbul']

    # Variables for each day (0..9 for days 1..10)
    # Each day can be in one city or transitioning between two
    day_city = [Int(f'day_{i}') for i in range(10)]
    is_transition = [Bool(f'trans_{i}') for i in range(10)]
    transition_from = [Int(f'trans_from_{i}') for i in range(10)]
    transition_to = [Int(f'trans_to_{i}') for i in range(10)]

    # Initial constraints
    for i in range(10):
        s.add(day_city[i] >= 0, day_city[i] <= 2)
        s.add(Implies(is_transition[i], 
                     And(transition_from[i] >= 0, transition_from[i] <= 2,
                         transition_to[i] >= 0, transition_to[i] <= 2,
                         transition_from[i] != transition_to[i])))
        s.add(Implies(Not(is_transition[i]), 
                     And(transition_from[i] == day_city[i],
                         transition_to[i] == day_city[i])))

    # Flight connections
    for i in range(10):
        s.add(Or(
            Not(is_transition[i]),  # Not a transition day
            # Valid transitions:
            And(transition_from[i] == London, transition_to[i] == Istanbul),
            And(transition_from[i] == Istanbul, transition_to[i] == London),
            And(transition_from[i] == London, transition_to[i] == Santorini),
            And(transition_from[i] == Santorini, transition_to[i] == London)
        ))

    # Consistency between days
    for i in range(9):
        s.add(Or(
            # Stay in same city
            And(day_city[i] == day_city[i+1], Not(is_transition[i]), Not(is_transition[i+1])),
            # Transition from city A to B
            And(day_city[i] == transition_from[i], 
                day_city[i+1] == transition_to[i],
                is_transition[i])
        ))

    # Count days in each city (including transition days)
    london_days = Sum([If(Or(day_city[i] == London,
                           And(is_transition[i], 
                               Or(transition_from[i] == London,
                                  transition_to[i] == London))), 1, 0) 
                    for i in range(10)])
    santorini_days = Sum([If(Or(day_city[i] == Santorini,
                               And(is_transition[i],
                                   Or(transition_from[i] == Santorini,
                                      transition_to[i] == Santorini))), 1, 0)
                        for i in range(10)])
    istanbul_days = Sum([If(Or(day_city[i] == Istanbul,
                              And(is_transition[i],
                                  Or(transition_from[i] == Istanbul,
                                     transition_to[i] == Istanbul))), 1, 0)
                       for i in range(10)])

    s.add(london_days == 3)
    s.add(santorini_days == 6)
    s.add(istanbul_days == 3)

    # Conference days must be in Santorini (not transition days)
    s.add(And(day_city[4] == Santorini, Not(is_transition[4])))  # Day 5
    s.add(And(day_city[9] == Santorini, Not(is_transition[9])))  # Day 10

    # Contiguous stays
    # Ensure London stay is contiguous (3 consecutive days)
    # We'll add a constraint that there exists a 3-day window where all days are London
    london_window = Or([And(day_city[i] == London,
                           day_city[i+1] == London,
                           day_city[i+2] == London,
                           Not(is_transition[i]),
                           Not(is_transition[i+1]),
                           Not(is_transition[i+2]))
                      for i in range(8)])
    s.add(london_window)

    if s.check() == sat:
        model = s.model()
        itinerary = []
        for i in range(10):
            if is_true(model.eval(is_transition[i])):
                from_city = city_names[model.eval(transition_from[i]).as_long()]
                to_city = city_names[model.eval(transition_to[i]).as_long()]
                itinerary.append({"day": i+1, "place": f"{from_city}→{to_city}"})
            else:
                city = city_names[model.eval(day_city[i]).as_long()]
                itinerary.append({"day": i+1, "place": city})
        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

itinerary = solve_itinerary()
print(itinerary)