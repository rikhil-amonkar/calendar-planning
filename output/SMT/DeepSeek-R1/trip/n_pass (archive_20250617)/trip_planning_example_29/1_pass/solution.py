import z3

def main():
    # Create solver
    s = z3.Solver()
    
    # City mapping: 0=Frankfurt, 1=Krakow, 2=Dubrovnik
    n_days = 10
    days = list(range(1, n_days+1))
    
    # Variables for the start location of each day
    loc_start = [z3.Int(f'loc_start_{d}') for d in days]
    # Variables for flight each day: -1 means no flight, otherwise the destination city
    flight = [z3.Int(f'flight_{d}') for d in days]
    
    # Constraint: loc_start for each day must be 0, 1, or 2
    for d in days:
        s.add(z3.Or(loc_start[d-1] == 0, loc_start[d-1] == 1, loc_start[d-1] == 2))
        s.add(z3.Or(flight[d-1] == -1, flight[d-1] == 0, flight[d-1] == 1, flight[d-1] == 2))
    
    # Constraint: for days 1 to 9, next day's start is flight destination if flight, else same as current
    for d in range(1, n_days):
        s.add(loc_start[d] == z3.If(flight[d-1] != -1, flight[d-1], loc_start[d-1]))
    
    # Flight constraints: if flying, must be to a connected city
    for d in range(0, n_days):
        # Condition when flight is taken
        cond = flight[d] != -1
        # Allowed flights:
        #   From Frankfurt (0): can fly to Krakow (1) or Dubrovnik (2)
        #   From Krakow (1): can fly to Frankfurt (0)
        #   From Dubrovnik (2): can fly to Frankfurt (0)
        s.add(z3.Implies(cond, 
                         z3.Or(
                             z3.And(loc_start[d] == 0, z3.Or(flight[d] == 1, flight[d] == 2)),
                             z3.And(loc_start[d] == 1, flight[d] == 0),
                             z3.And(loc_start[d] == 2, flight[d] == 0)
                         )))
        # Cannot fly to the same city
        s.add(z3.Implies(cond, loc_start[d] != flight[d]))
    
    # Exactly two flights
    flight_indicators = [z3.If(flight[d] != -1, 1, 0) for d in range(0, n_days)]
    s.add(sum(flight_indicators) == 2)
    
    # Presence in each city each day
    # in_city[city, d] = (loc_start[d] == city) or (flight[d] != -1 and flight[d] == city)
    in_city = {}
    for city in [0,1,2]:
        for d in range(0, n_days):
            in_city[(city, d)] = z3.Or(loc_start[d] == city, 
                                        z3.And(flight[d] != -1, flight[d] == city))
    
    # Total days in each city
    total_frankfurt = z3.Sum([z3.If(in_city[(0, d)], 1, 0) for d in range(0, n_days)])
    total_krakow = z3.Sum([z3.If(in_city[(1, d)], 1, 0) for d in range(0, n_days)])
    total_dubrovnik = z3.Sum([z3.If(in_city[(2, d)], 1, 0) for d in range(0, n_days)])
    
    s.add(total_frankfurt == 3)
    s.add(total_krakow == 2)
    s.add(total_dubrovnik == 7)
    
    # Must be in Krakow on day 9 and 10 (which are index 8 and 9)
    s.add(in_city[(1, 8)] == True)  # Day 9
    s.add(in_city[(1, 9)] == True)  # Day 10
    
    # Check and get the model
    if s.check() == z3.sat:
        model = s.model()
        city_names = {0: "Frankfurt", 1: "Krakow", 2: "Dubrovnik"}
        
        # Print the plan
        for d in range(0, n_days):
            start_val = model[loc_start[d]].as_long()
            flight_val = model[flight[d]].as_long()
            start_city = city_names[start_val]
            
            if flight_val == -1:
                action = f"Stay in {start_city}"
                present = [start_city]
            else:
                dest_city = city_names[flight_val]
                action = f"Fly from {start_city} to {dest_city}"
                present = [start_city, dest_city]
            
            print(f"Day {d+1}: Start in {start_city}. {action}. Present in {', '.join(present)}.")
    else:
        print("No valid plan found.")

if __name__ == "__main__":
    main()