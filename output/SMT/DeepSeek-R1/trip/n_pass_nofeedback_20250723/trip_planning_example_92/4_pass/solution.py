from z3 import Solver, Int, Or, And, If, sat
import json

def main():
    solver = Solver()
    city_names = {0: "Dublin", 1: "Riga", 2: "Vilnius"}
    allowed_flights = [(0, 1), (1, 0), (1, 2), (2, 1)]
    
    s = [Int(f's_{i}') for i in range(12)]
    e = [Int(f'e_{i}') for i in range(12)]
    
    solver.add(s[0] == 0)
    solver.add(e[11] == 2)
    
    for i in range(12):
        solver.add(s[i] >= 0, s[i] <= 2)
        solver.add(e[i] >= 0, e[i] <= 2)
    
    for i in range(11):
        solver.add(e[i] == s[i+1])
    
    for i in range(12):
        no_flight = (s[i] == e[i])
        flight_options = Or(
            And(s[i] == 0, e[i] == 1),
            And(s[i] == 1, e[i] == 0),
            And(s[i] == 1, e[i] == 2),
            And(s[i] == 2, e[i] == 1)
        )
        solver.add(Or(no_flight, flight_options))
    
    dublin_count = 0
    riga_count = 0
    vilnius_count = 0
    
    for i in range(12):
        dublin_count += If(Or(s[i] == 0, e[i] == 0), 1, 0)
        riga_count += If(Or(s[i] == 1, e[i] == 1), 1, 0)
        vilnius_count += If(Or(s[i] == 2, e[i] == 2), 1, 0)
    
    solver.add(dublin_count == 2)
    solver.add(riga_count == 5)
    solver.add(vilnius_count == 7)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(12):
            start_val = model[s[i]].as_long()
            end_val = model[e[i]].as_long()
            if start_val == end_val:
                place = city_names[start_val]
            else:
                place = [city_names[start_val], city_names[end_val]]
            itinerary.append({'day_range': f'Day {i+1}', 'place': place})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()