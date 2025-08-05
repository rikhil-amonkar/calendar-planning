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
    
    # Allowed flights (directed)
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
        (Zurich, Florence)  # Only Zurich->Florence
    ]

    # Create Z3 variables
    s = [Int(f's_{i}') for i in range(26)]  # start city each day (0-25)
    d_last = Int('d_last')  # end city on day 26

    solver = Solver()

    # City indices constraint
    for i in range(26):
        solver.add(s[i] >= 0, s[i] <= 6)
    solver.add(d_last >= 0, d_last <= 6)

    # Flight constraints for days 0-24
    for i in range(25):
        # Create disjunction for allowed flights
        flight_options = []
        for (a, b) in allowed_flights:
            flight_options.append(And(s[i] == a, s[i+1] == b))
        solver.add(Or(
            s[i] == s[i+1],  # Stay in same city
            And(s[i] != s[i+1], Or(flight_options))  # Fly to new city
        ))
    
    # Flight constraint for day 25 to day 26
    flight_options_last = []
    for (a, b) in allowed_flights:
        flight_options_last.append(And(s[25] == a, d_last == b))
    solver.add(Or(
        s[25] == d_last,  # Stay in same city
        And(s[25] != d_last, Or(flight_options_last))  # Fly to new city
    ))

    # Presence variables: presence[day][city] for days 1-26
    presence = [[Bool(f'presence_{d}_{c}') for c in range(7)] for d in range(26)]
    
    # Define presence constraints
    for d in range(25):  # Days 1-25
        for c in range(7):
            # Presence if either start or end city matches
            solver.add(presence[d][c] == Or(s[d] == c, s[d+1] == c))
    
    # Day 26 presence
    for c in range(7):
        solver.add(presence[25][c] == Or(s[25] == c, d_last == c))

    # Total days per city
    total_days = [Int(f'total_{city_names[c]}') for c in range(7)]
    for c in range(7):
        solver.add(total_days[c] == Sum([If(presence[d][c], 1, 0) for d in range(26)]))
    
    # Set total days constraints
    solver.add(total_days[Bucharest] == 3)
    solver.add(total_days[Venice] == 5)
    solver.add(total_days[Prague] == 4)
    solver.add(total_days[Frankfurt] == 5)
    solver.add(total_days[Zurich] == 5)
    solver.add(total_days[Florence] == 5)
    solver.add(total_days[Tallinn] == 5)

    # Event constraints (using 0-indexed day indices for presence array)
    # Days 22-26: presence indices 21-25
    venice_event = Or(presence[21][Venice], presence[22][Venice], 
                      presence[23][Venice], presence[24][Venice], presence[25][Venice])
    # Days 12-16: presence indices 11-15
    frankfurt_event = Or(presence[11][Frankfurt], presence[12][Frankfurt], 
                         presence[13][Frankfurt], presence[14][Frankfurt], presence[15][Frankfurt])
    # Days 8-12: presence indices 7-11
    tallinn_event = Or(presence[7][Tallinn], presence[8][Tallinn], 
                       presence[9][Tallinn], presence[10][Tallinn], presence[11][Tallinn])

    solver.add(venice_event)
    solver.add(frankfurt_event)
    solver.add(tallinn_event)

    # Solve and output
    if solver.check() == sat:
        model = solver.model()
        s_val = [model.evaluate(s[i]).as_long() for i in range(26)]
        d_last_val = model.evaluate(d_last).as_long()
        
        itinerary = []
        for day in range(1, 26):  # Days 1-25
            start_city = s_val[day-1]
            end_city = s_val[day]
            if start_city == end_city:
                itinerary.append({"day": day, "city": city_names[start_city]})
            else:
                itinerary.append({"day": day, "city": [city_names[start_city], city_names[end_city]]})
        
        # Day 26
        if s_val[25] == d_last_val:
            itinerary.append({"day": 26, "city": city_names[s_val[25]]})
        else:
            itinerary.append({"day": 26, "city": [city_names[s_val[25]], city_names[d_last_val]]})
        
        import json
        print(json.dumps({"itinerary": itinerary}, indent=2))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()