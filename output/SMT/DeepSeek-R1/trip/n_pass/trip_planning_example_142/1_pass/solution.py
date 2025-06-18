import z3
import json

def main():
    # Define the City datatype
    City = z3.Datatype('City')
    City.declare('Madrid')
    City.declare('Dublin')
    City.declare('Tallinn')
    City = City.create()

    # Create variables for 7 days
    s = [z3.Const(f's_{i}', City) for i in range(7)]  # starting city on day i (0-indexed, representing day1 to day7)
    e = [z3.Const(f'e_{i}', City) for i in range(7)]  # ending city on day i
    fly = [z3.Bool(f'fly_{i}') for i in range(7)]     # whether we fly on day i

    solver = z3.Solver()

    # Constraint: if no flight, start and end city must be the same
    for i in range(7):
        solver.add(z3.Implies(z3.Not(fly[i]), s[i] == e[i]))

    # Constraint: if flight, must be between connected cities
    for i in range(7):
        solver.add(z3.Implies(fly[i], 
                   z3.Or(
                       z3.And(s[i] == City.Madrid, e[i] == City.Dublin),
                       z3.And(s[i] == City.Dublin, e[i] == City.Madrid),
                       z3.And(s[i] == City.Dublin, e[i] == City.Tallinn),
                       z3.And(s[i] == City.Tallinn, e[i] == City.Dublin)
                   )))

    # Constraint: next day's start is previous day's end
    for i in range(1, 7):
        solver.add(s[i] == e[i-1])

    # Constraint: must be in Tallinn on day6 and day7 (indices 5 and 6)
    solver.add(z3.Or(s[5] == City.Tallinn, e[5] == City.Tallinn))
    solver.add(z3.Or(s[6] == City.Tallinn, e[6] == City.Tallinn))

    # Total days constraints
    in_madrid = [z3.Or(s[i] == City.Madrid, e[i] == City.Madrid) for i in range(7)]
    in_dublin = [z3.Or(s[i] == City.Dublin, e[i] == City.Dublin) for i in range(7)]
    in_tallinn = [z3.Or(s[i] == City.Tallinn, e[i] == City.Tallinn) for i in range(7)]
    total_madrid = z3.Sum([z3.If(cond, 1, 0) for cond in in_madrid])
    total_dublin = z3.Sum([z3.If(cond, 1, 0) for cond in in_dublin])
    total_tallinn = z3.Sum([z3.If(cond, 1, 0) for cond in in_tallinn])
    solver.add(total_madrid == 4, total_dublin == 3, total_tallinn == 2)

    # Solve the problem
    if solver.check() == z3.sat:
        model = solver.model()
        s_vals = [model.eval(s_i) for s_i in s]
        e_vals = [model.eval(e_i) for e_i in e]
        fly_vals = [model.eval(fly_i) for fly_i in fly]

        def city_to_str(city_val):
            if city_val.eq(City.Madrid):
                return "Madrid"
            elif city_val.eq(City.Dublin):
                return "Dublin"
            elif city_val.eq(City.Tallinn):
                return "Tallinn"
            else:
                return "Unknown"

        segments = []  # (start_day, end_day, city)
        current_city = city_to_str(s_vals[0])
        start_day = 1
        for i in range(7):
            if fly_vals[i]:
                flight_day = i + 1
                segments.append((start_day, flight_day, current_city))
                current_city = city_to_str(e_vals[i])
                start_day = flight_day
        segments.append((start_day, 7, current_city))

        itinerary = []
        for idx, seg in enumerate(segments):
            start, end, city = seg
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
            
            if idx < len(segments) - 1:
                # Add the flight day breakdown: departure and arrival
                day_break = end
                itinerary.append({"day_range": f"Day {day_break}", "place": city})
                next_city = segments[idx+1][2]
                itinerary.append({"day_range": f"Day {day_break}", "place": next_city})
        
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No solution found"}))

if __name__ == '__main__':
    main()