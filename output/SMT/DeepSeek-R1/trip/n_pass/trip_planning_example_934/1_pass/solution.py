from z3 import *

def main():
    # Define the cities
    city_names = ['Brussels', 'Rome', 'Dubrovnik', 'Geneva', 'Budapest', 'Riga', 'Valencia']
    CitySort, city_consts = EnumSort('City', city_names)
    Brussels, Rome, Dubrovnik, Geneva, Budapest, Riga, Valencia = city_consts
    city_dict = {name: const for name, const in zip(city_names, city_consts)}
    
    # Define direct flights (undirected edges)
    direct_flights_undir = [
        ('Brussels','Valencia'),
        ('Rome','Valencia'),
        ('Brussels','Geneva'),
        ('Rome','Geneva'),
        ('Dubrovnik','Geneva'),
        ('Valencia','Geneva'),
        ('Rome','Riga'),
        ('Geneva','Budapest'),
        ('Riga','Brussels'),
        ('Rome','Budapest'),
        ('Rome','Brussels'),
        ('Brussels','Budapest'),
        ('Dubrovnik','Rome')
    ]
    
    # Remove duplicates by using a set of sorted tuples
    undir_set = set()
    for u, v in direct_flights_undir:
        key = tuple(sorted([u, v]))
        undir_set.add(key)
    
    # Create directed flights (both directions)
    directed_flights = []
    for u, v in undir_set:
        directed_flights.append((u, v))
        directed_flights.append((v, u))
    
    # Convert to Z3 constants
    z3_directed_flights = []
    for u_str, v_str in directed_flights:
        u_const = city_dict[u_str]
        v_const = city_dict[v_str]
        z3_directed_flights.append((u_const, v_const))
    
    # Create Z3 variables for each day (1 to 17)
    start_city = [None] * 18  # index 0 unused
    travel = [None] * 18
    end_city = [None] * 18
    
    for i in range(1, 18):
        start_city[i] = Const(f'start_city_{i}', CitySort)
        travel[i] = Bool(f'travel_{i}')
        end_city[i] = Const(f'end_city_{i}', CitySort)
    
    s = Solver()
    
    # Continuity constraint: start_city[i+1] = end_city[i] for i in 1..16
    for i in range(1, 17):
        s.add(start_city[i+1] == end_city[i])
    
    # Travel constraints for each day
    for i in range(1, 18):
        c1 = start_city[i]
        t = travel[i]
        c2 = end_city[i]
        
        # If traveling, c1 != c2 and (c1, c2) must be in directed flights
        flight_conds = []
        for (u, v) in z3_directed_flights:
            flight_conds.append(And(c1 == u, c2 == v))
        s.add(If(t, 
                 And(c1 != c2, Or(flight_conds)),
                 c2 == c1))
    
    # Total travel days must be 6
    total_travel = Sum([If(travel[i], 1, 0) for i in range(1, 18)])
    s.add(total_travel == 6)
    
    # Constraints for days in each city
    req_days = {
        'Brussels': 5,
        'Rome': 2,
        'Dubrovnik': 3,
        'Geneva': 5,
        'Budapest': 2,
        'Riga': 4,
        'Valencia': 2
    }
    
    for city_name, req in req_days.items():
        city_const = city_dict[city_name]
        total = 0
        for i in range(1, 18):
            in_city = Or(start_city[i] == city_const, And(travel[i], end_city[i] == city_const))
            total += If(in_city, 1, 0)
        s.add(total == req)
    
    # Event constraints
    # Brussels workshop between days 7-11 (inclusive)
    brussels_workshop = []
    for i in range(7, 12):  # days 7 to 11
        in_brussels = Or(start_city[i] == Brussels, And(travel[i], end_city[i] == Brussels))
        brussels_workshop.append(in_brussels)
    s.add(Or(brussels_workshop))
    
    # Budapest meeting between days 16-17
    budapest_meeting = []
    for i in range(16, 18):  # days 16 and 17
        in_budapest = Or(start_city[i] == Budapest, And(travel[i], end_city[i] == Budapest))
        budapest_meeting.append(in_budapest)
    s.add(Or(budapest_meeting))
    
    # Riga meeting between days 4-7
    riga_meeting = []
    for i in range(4, 8):  # days 4 to 7
        in_riga = Or(start_city[i] == Riga, And(travel[i], end_city[i] == Riga))
        riga_meeting.append(in_riga)
    s.add(Or(riga_meeting))
    
    # Check and get the model
    if s.check() == sat:
        m = s.model()
        # Helper to get city name from constant
        def get_city_name(c):
            for name, const in city_dict.items():
                if m.eval(const).eq(m.eval(c)):
                    return name
            return "Unknown"
        
        # Print the itinerary
        print("Day\tStart City\tTravel?\tEnd City\tCities Visited")
        for i in range(1, 18):
            sc_val = m.eval(start_city[i])
            t_val = m.eval(travel[i])
            ec_val = m.eval(end_city[i])
            sc_name = get_city_name(sc_val)
            ec_name = get_city_name(ec_val)
            if is_true(t_val):
                visited = f"{sc_name}, {ec_name}"
            else:
                visited = sc_name
            print(f"{i}\t{sc_name}\t{is_true(t_val)}\t{ec_name}\t{visited}")
    else:
        print("No solution found")

if __name__ == "__main__":
    main()