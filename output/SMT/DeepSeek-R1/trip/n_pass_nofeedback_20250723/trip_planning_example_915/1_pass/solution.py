from z3 import *

def main():
    # City indices
    Bucharest = 0
    Venice = 1
    Prague = 2
    Frankfurt = 3
    Zurich = 4
    Florence = 5
    Tallinn = 6

    city_names = ["Bucharest", "Venice", "Prague", "Frankfurt", "Zurich", "Florence", "Tallinn"]
    
    # Define the allowed flights (directed)
    allowed_flights = [
        (Bucharest, Frankfurt), (Frankfurt, Bucharest),
        (Bucharest, Prague), (Prague, Bucharest),
        (Bucharest, Zurich), (Zurich, Bucharest),
        (Venice, Frankfurt), (Frankfurt, Venice),
        (Venice, Zurich), (Zurich, Venice),
        (Prague, Tallinn), (Tallinn, Prague),
        (Prague, Zurich), (Zurich, Prague),
        (Prague, Florence), (Florence, Prague),
        (Frankfurt, Tallinn), (Tallinn, Frankfurt),
        (Frankfurt, Zurich), (Zurich, Frankfurt),
        (Frankfurt, Florence), (Florence, Frankfurt),
        (Prague, Frankfurt), (Frankfurt, Prague),
        (Zurich, Tallinn), (Tallinn, Zurich),
        (Zurich, Florence)  # Only from Zurich to Florence
    ]

    # Create Z3 variables
    s = [Int('s_%d' % i) for i in range(26)]  # start city for each day (26 days, index 0 to 25)
    d_last = Int('d_last')  # end city for the last day (day26)

    solver = Solver()

    # Constraint: all s[i] and d_last are between 0 and 6
    for i in range(26):
        solver.add(s[i] >= 0, s[i] <= 6)
    solver.add(d_last >= 0, d_last <= 6)

    # Flight constraints for days 0 to 24: either stay or fly with a direct flight
    for i in range(25):
        stay = (s[i] == s[i+1])
        fly = And(s[i] != s[i+1], Or([And(s[i] == a, s[i+1] == b) for (a, b) in allowed_flights]))
        solver.add(Or(stay, fly))

    # Flight constraint for the last day (day25 to day26)
    stay_last = (s[25] == d_last)
    fly_last = And(s[25] != d_last, Or([And(s[25] == a, d_last == b) for (a, b) in allowed_flights]))
    solver.add(Or(stay_last, fly_last))

    # Function to compute total days for a city j
    def total_days(j):
        total = 0
        # Count the starts: for each day i, if s[i] == j, add 1.
        for i in range(26):
            total += If(s[i] == j, 1, 0)
        # For the first 25 days: count the flight ends (if flight and end city is j, then add 1)
        for i in range(25):
            total += If(And(s[i] != s[i+1], s[i+1] == j), 1, 0)
        # For the last day: if flight and d_last is j, add 1.
        total += If(And(s[25] != d_last, d_last == j), 1, 0)
        return total

    # Total days constraints
    solver.add(total_days(Bucharest) == 3)
    solver.add(total_days(Venice) == 5)
    solver.add(total_days(Prague) == 4)
    solver.add(total_days(Frankfurt) == 5)
    solver.add(total_days(Zurich) == 5)
    solver.add(total_days(Florence) == 5)
    solver.add(total_days(Tallinn) == 5)

    # Event constraints: presence in the city on at least one day in the event window.
    # Venice (index1) between day22 (index21) and day26 (index25)
    venice_event = Or([Or(s[i] == Venice, 
                         If(i < 25, And(s[i] != s[i+1], s[i+1] == Venice),
                             And(s[25] != d_last, d_last == Venice))) 
                    for i in range(21, 26)])
    solver.add(venice_event)

    # Frankfurt (index3) between day12 (index11) and day16 (index15)
    frankfurt_event = Or([Or(s[i] == Frankfurt,
                            If(i < 25, And(s[i] != s[i+1], s[i+1] == Frankfurt),
                                And(s[25] != d_last, d_last == Frankfurt)))
                        for i in range(11, 16)])
    solver.add(frankfurt_event)

    # Tallinn (index6) between day8 (index7) and day12 (index11)
    tallinn_event = Or([Or(s[i] == Tallinn,
                          If(i < 25, And(s[i] != s[i+1], s[i+1] == Tallinn),
                              And(s[25] != d_last, d_last == Tallinn)))
                      for i in range(7, 12)])
    solver.add(tallinn_event)

    # Check and get the model
    if solver.check() == sat:
        model = solver.model()
        # Get the values for s[0..25] and d_last
        s_val = [model.evaluate(s[i]).as_long() for i in range(26)]
        d_last_val = model.evaluate(d_last).as_long()
        
        # Build the itinerary
        itinerary = []
        # For days 0 to 24
        for i in range(25):
            start_city = s_val[i]
            end_city = s_val[i+1]
            if start_city == end_city:
                # No flight: only one city
                itinerary.append({"day": i+1, "city": city_names[start_city]})
            else:
                # Flight: two cities
                itinerary.append({"day": i+1, "city": [city_names[start_city], city_names[end_city]]})
        # Day 25 (last day)
        if s_val[25] == d_last_val:
            itinerary.append({"day": 26, "city": city_names[s_val[25]]})
        else:
            itinerary.append({"day": 26, "city": [city_names[s_val[25]], city_names[d_last_val]]})
        
        # Output as JSON
        import json
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()