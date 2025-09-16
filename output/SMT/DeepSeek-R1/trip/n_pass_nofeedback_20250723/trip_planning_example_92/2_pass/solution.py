from z3 import Solver, Int, Or, And, If, sat
import json

def main():
    solver = Solver()
    city_names = {0: "Dublin", 1: "Riga", 2: "Vilnius"}
    allowed_flights = [(0, 1), (1, 0), (1, 2)]
    
    s = [Int(f's_{i}') for i in range(12)]
    e12 = Int('e12')
    
    for i in range(12):
        solver.add(s[i] >= 0, s[i] <= 2)
    solver.add(e12 >= 0, e12 <= 2)
    
    for i in range(11):
        no_flight = (s[i] == s[i+1])
        flight_options = Or([And(s[i] == a, s[i+1] == b) for a, b in allowed_flights])
        solver.add(Or(no_flight, flight_options))
    
    no_flight12 = (s[11] == e12)
    flight_options12 = Or([And(s[11] == a, e12 == b) for a, b in allowed_flights])
    solver.add(Or(no_flight12, flight_options12))
    
    dublin_count = 0
    riga_count = 0
    vilnius_count = 0
    
    for i in range(11):
        same = (s[i] == s[i+1])
        dublin_count += If(same, 
                          If(s[i] == 0, 1, 0),
                          If(s[i] == 0, 1, 0) + If(s[i+1] == 0, 1, 0))
        riga_count += If(same,
                         If(s[i] == 1, 1, 0),
                         If(s[i] == 1, 1, 0) + If(s[i+1] == 1, 1, 0))
        vilnius_count += If(same,
                            If(s[i] == 2, 1, 0),
                            If(s[i] == 2, 1, 0) + If(s[i+1] == 2, 1, 0))
    
    same12 = (s[11] == e12)
    dublin_count += If(same12,
                      If(s[11] == 0, 1, 0),
                      If(s[11] == 0, 1, 0) + If(e12 == 0, 1, 0))
    riga_count += If(same12,
                     If(s[11] == 1, 1, 0),
                     If(s[11] == 1, 1, 0) + If(e12 == 1, 1, 0))
    vilnius_count += If(same12,
                        If(s[11] == 2, 1, 0),
                        If(s[11] == 2, 1, 0) + If(e12 == 2, 1, 0))
    
    solver.add(dublin_count == 2)
    solver.add(riga_count == 5)
    solver.add(vilnius_count == 7)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for day in range(1, 13):
            if day <= 11:
                start_val = model[s[day-1]].as_long()
                end_val = model[s[day]].as_long()
                if start_val == end_val:
                    place = city_names[start_val]
                else:
                    place = [city_names[start_val], city_names[end_val]]
            else:
                start_val = model[s[11]].as_long()
                end_val = model[e12].as_long()
                if start_val == end_val:
                    place = city_names[start_val]
                else:
                    place = [city_names[start_val], city_names[end_val]]
            itinerary.append({'day_range': f'Day {day}', 'place': place})
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()