import z3

def main():
    s = z3.Solver()
    
    # City encoding: 0=Frankfurt, 1=Krakow, 2=Dubrovnik
    n_days = 10
    days = list(range(n_days))
    
    # Location at the start of each day
    loc_start = [z3.Int(f'loc_start_{d}') for d in days]
    # Flight action: -1 = no flight, otherwise destination city
    flight = [z3.Int(f'flight_{d}') for d in days]
    
    # City constraints: must be 0, 1, or 2
    for d in days:
        s.add(z3.Or(loc_start[d] == 0, loc_start[d] == 1, loc_start[d] == 2))
        s.add(z3.Or(flight[d] == -1, 
                   flight[d] == 0, 
                   flight[d] == 1, 
                   flight[d] == 2))
    
    # Location transitions
    for d in range(0, n_days-1):
        s.add(loc_start[d+1] == z3.If(flight[d] != -1, flight[d], loc_start[d]))
    
    # Flight validity rules
    for d in range(0, n_days):
        flight_taken = flight[d] != -1
        frankfurt_flights = z3.And(loc_start[d] == 0, 
                                  z3.Or(flight[d] == 1, flight[d] == 2))
        krakow_flights = z3.And(loc_start[d] == 1, flight[d] == 0)
        dubrovnik_flights = z3.And(loc_start[d] == 2, flight[d] == 0)
        
        s.add(z3.Implies(flight_taken, 
                         z3.Or(frankfurt_flights, krakow_flights, dubrovnik_flights)))
        # Cannot fly to same city
        s.add(z3.Implies(flight_taken, loc_start[d] != flight[d]))
    
    # Exactly three flights total
    flight_days = [z3.If(flight[d] != -1, 1, 0) for d in range(0, n_days)]
    s.add(sum(flight_days) == 3)
    
    # Presence in each city per day
    in_city = {}
    for city in [0, 1, 2]:
        for d in range(0, n_days):
            in_city[(city, d)] = z3.Or(loc_start[d] == city, 
                                       z3.And(flight[d] != -1, flight[d] == city))
    
    # Total days per city
    total_days = [0, 0, 0]
    for city in [0, 1, 2]:
        total_days[city] = z3.Sum([z3.If(in_city[(city, d)], 1, 0) for d in range(0, n_days)])
    
    s.add(total_days[1] == 2)  # Krakow
    s.add(total_days[2] == 7)  # Dubrovnik
    s.add(total_days[0] == 3)  # Frankfurt
    
    # Must be in Krakow on days 9 and 10 (indices 8 and 9)
    s.add(in_city[(1, 8)])
    s.add(in_city[(1, 9)])
    
    # Start and end in Dubrovnik
    s.add(loc_start[0] == 2)  # Start day 1
    s.add(z3.Or(
        z3.And(flight[9] == -1, loc_start[9] == 2),
        flight[9] == 2
    ))
    
    # Check for solution
    if s.check() == z3.sat:
        model = s.model()
        city_names = {0: "Frankfurt", 1: "Krakow", 2: "Dubrovnik"}
        
        print("Valid plan found:")
        for d in range(0, n_days):
            start_val = model[loc_start[d]].as_long()
            flight_val = model[flight[d]].as_long()
            start_city = city_names[start_val]
            
            if flight_val == -1:
                action = f"Stay in {start_city}"
                present_cities = [start_city]
            else:
                dest_city = city_names[flight_val]
                action = f"Fly from {start_city} to {dest_city}"
                present_cities = [start_city, dest_city]
            
            present_str = ", ".join(sorted(present_cities))
            print(f"Day {d+1}: Start in {start_city}. {action}. Present in {present_str}.")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()