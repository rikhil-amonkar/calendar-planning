import z3
import json

def main():
    # Create solver
    solver = z3.Solver()
    
    # City mapping: 0=Dublin, 1=Riga, 2=Vilnius
    city_names = {0: "Dublin", 1: "Riga", 2: "Vilnius"}
    
    # Allowed flights: (start, end)
    allowed_flights = [(0, 1), (1, 0), (1, 2)]
    
    # Create variables for start and end cities for 12 days
    s = [z3.Int(f's_{i}') for i in range(12)]
    e = [z3.Int(f'e_{i}') for i in range(12)]
    
    # Constraints: each city variable is in {0,1,2}
    for i in range(12):
        solver.add(s[i] >= 0, s[i] <= 2)
        solver.add(e[i] >= 0, e[i] <= 2)
    
    # Flight constraints: either no flight or an allowed flight
    for i in range(12):
        no_flight = s[i] == e[i]
        flight_options = [z3.And(s[i] == a, e[i] == b) for (a, b) in allowed_flights]
        solver.add(z3.Or(no_flight, *flight_options))
    
    # Continuity: end of day i must equal start of day i+1
    for i in range(11):
        solver.add(e[i] == s[i+1])
    
    # Count days for each city
    count_dublin = 0
    count_riga = 0
    count_vilnius = 0
    
    for i in range(12):
        # Count start city
        count_dublin += z3.If(s[i] == 0, 1, 0)
        count_riga += z3.If(s[i] == 1, 1, 0)
        count_vilnius += z3.If(s[i] == 2, 1, 0)
        
        # Count end city only if it's a flight day (start != end)
        count_dublin += z3.If(z3.And(s[i] != e[i], e[i] == 0), 1, 0)
        count_riga += z3.If(z3.And(s[i] != e[i], e[i] == 1), 1, 0)
        count_vilnius += z3.If(z3.And(s[i] != e[i], e[i] == 2), 1, 0)
    
    # Add constraints for total days in each city
    solver.add(count_dublin == 2)
    solver.add(count_riga == 5)
    solver.add(count_vilnius == 7)
    
    # Check for a solution
    if solver.check() == z3.sat:
        model = solver.model()
        itinerary = []
        for i in range(12):
            start_val = model.eval(s[i]).as_long()
            end_val = model.eval(e[i]).as_long()
            if start_val == end_val:
                day_cities = [city_names[start_val]]
            else:
                day_cities = [city_names[start_val], city_names[end_val]]
            itinerary.append(day_cities)
        
        result = {'itinerary': itinerary}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()