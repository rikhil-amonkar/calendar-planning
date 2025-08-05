from z3 import *

def main():
    # Define the days and cities
    n_days = 11
    cities = {'Krakow': 0, 'Paris': 1, 'Seville': 2}
    city_names = {0: 'Krakow', 1: 'Paris', 2: 'Seville'}
    
    # Create Z3 variables
    s = [Int('s_%d' % i) for i in range(1, n_days+1)]
    flight = [Bool('flight_%d' % i) for i in range(1, n_days+1)]
    e = [Int('e_%d' % i) for i in range(1, n_days+1)]
    
    solver = Solver()
    
    # City constraints: s[i] and e[i] must be 0, 1, or 2
    for i in range(n_days):
        solver.add(s[i] >= 0, s[i] <= 2)
        solver.add(e[i] >= 0, e[i] <= 2)
    
    # Flight constraints
    for i in range(n_days):
        # If flight, then e[i] must be a direct neighbor of s[i]
        solver.add(Implies(flight[i], 
                          Or(
                              And(s[i] == 0, e[i] == 1),
                              And(s[i] == 1, e[i] == 0),
                              And(s[i] == 1, e[i] == 2),
                              And(s[i] == 2, e[i] == 1)
                          )))
        # If no flight, then e[i] must equal s[i]
        solver.add(Implies(Not(flight[i]), e[i] == s[i]))
    
    # Consecutive day constraints: s[i+1] must equal e[i]
    for i in range(n_days - 1):
        solver.add(s[i+1] == e[i])
    
    # Count days per city
    days_in_city = [0, 0, 0]  # Krakow, Paris, Seville
    for i in range(n_days):
        in_krakow = Or(s[i] == 0, And(flight[i], e[i] == 0))
        in_paris = Or(s[i] == 1, And(flight[i], e[i] == 1))
        in_seville = Or(s[i] == 2, And(flight[i], e[i] == 2))
        days_in_city[0] += If(in_krakow, 1, 0)
        days_in_city[1] += If(in_paris, 1, 0)
        days_in_city[2] += If(in_seville, 1, 0)
    
    solver.add(days_in_city[0] == 5)
    solver.add(days_in_city[1] == 2)
    solver.add(days_in_city[2] == 6)
    
    # Workshop constraint: must be in Krakow on at least one of days 1-5
    workshop_constraint = Or([Or(s[i] == 0, And(flight[i], e[i] == 0)) for i in range(5)])
    solver.add(workshop_constraint)
    
    # Total flights should be 2 (since 5+2+6 = 13, and 13 - 11 = 2)
    total_flights = Sum([If(flight[i], 1, 0) for i in range(n_days)])
    solver.add(total_flights == 2)
    
    # Check and get the model
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
                cities_indices = sorted([s_val_int, e_val_int])
            else:
                cities_indices = [s_val_int]
            
            cities_list = [city_names[idx] for idx in cities_indices]
            itinerary.append(cities_list)
        
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()