from z3 import *

def main():
    n_days = 11
    city_names = {0: 'Krakow', 1: 'Paris', 2: 'Seville'}
    
    s = [Int('s_%d' % i) for i in range(1, n_days+1)]
    e = [Int('e_%d' % i) for i in range(1, n_days+1)]
    flight = [Bool('flight_%d' % i) for i in range(1, n_days+1)]
    
    solver = Solver()
    
    # Constraint: Start in Krakow on day 1
    solver.add(s[0] == 0)
    
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] <= 2)
        solver.add(e[i] >= 0, e[i] <= 2)
    
    # Flight constraints: only allow direct flights between connected cities
    for i in range(n_days):
        solver.add(Implies(flight[i], 
                          Or(
                              And(s[i] == 0, e[i] == 1),
                              And(s[i] == 1, e[i] == 0),
                              And(s[i] == 1, e[i] == 2),
                              And(s[i] == 2, e[i] == 1)
                          )))
        solver.add(Implies(Not(flight[i]), s[i] == e[i]))
    
    # Consecutive day constraint
    for i in range(n_days-1):
        solver.add(s[i+1] == e[i])
    
    # Count days in each city
    krakow_days = 0
    paris_days = 0
    seville_days = 0
    
    for i in range(n_days):
        # Count a day in a city if: 
        # - The day starts there, or 
        # - A flight ends there that day
        in_krakow = Or(s[i] == 0, And(flight[i], e[i] == 0))
        in_paris = Or(s[i] == 1, And(flight[i], e[i] == 1))
        in_seville = Or(s[i] == 2, And(flight[i], e[i] == 2))
        
        krakow_days = krakow_days + If(in_krakow, 1, 0)
        paris_days = paris_days + If(in_paris, 1, 0)
        seville_days = seville_days + If(in_seville, 1, 0)
    
    # Total days must be 5 in Krakow, 2 in Paris, 6 in Seville
    solver.add(krakow_days == 5)
    solver.add(paris_days == 2)
    solver.add(seville_days == 6)
    
    # Workshop constraint: at least one day in Krakow between days 1-5
    workshop_constraint = Or([Or(s[i] == 0, And(flight[i], e[i] == 0)) for i in range(5)])
    solver.add(workshop_constraint)
    
    # Total flights must be exactly 2
    total_flights = Sum([If(flight[i], 1, 0) for i in range(n_days)])
    solver.add(total_flights == 2)
    
    if solver.check() == sat:
        model = solver.model()
        itinerary = []
        for i in range(n_days):
            s_val = model.evaluate(s[i])
            e_val = model.evaluate(e[i])
            flight_val = model.evaluate(flight[i])
            s_val_int = s_val.as_long()
            e_val_int = e_val.as_long()
            flight_bool = is_true(flight_val)
            
            if flight_bool:
                # For flight days: list both cities in alphabetical order
                cities_list = sorted([city_names[s_val_int], city_names[e_val_int]])
            else:
                # For non-flight days: only the single city
                cities_list = [city_names[s_val_int]]
                
            itinerary.append(cities_list)
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()