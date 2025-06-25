from z3 import *

def main():
    # Mapping of cities to integers
    city_to_int = {
        'Paris': 0,
        'Stockholm': 1,
        'Vienna': 2,
        'Barcelona': 3,
        'Edinburgh': 4,
        'Krakow': 5,
        'Riga': 6,
        'Hamburg': 7
    }
    int_to_city = {v: k for k, v in city_to_int.items()}
    
    # Required days for each city (excluding Paris and Stockholm, which are fixed)
    req_days = {
        2: 4,   # Vienna
        3: 2,   # Barcelona
        4: 4,   # Edinburgh
        5: 3,   # Krakow
        6: 4,   # Riga
        7: 2    # Hamburg
    }
    
    # Direct flight pairs (as integers)
    direct_flights_pairs = [
        ('Hamburg', 'Stockholm'),
        ('Vienna', 'Stockholm'),
        ('Paris', 'Edinburgh'),
        ('Riga', 'Barcelona'),
        ('Paris', 'Riga'),
        ('Krakow', 'Barcelona'),
        ('Edinburgh', 'Stockholm'),
        ('Paris', 'Krakow'),
        ('Krakow', 'Stockholm'),
        ('Riga', 'Edinburgh'),
        ('Barcelona', 'Stockholm'),
        ('Paris', 'Stockholm'),
        ('Krakow', 'Edinburgh'),
        ('Vienna', 'Hamburg'),
        ('Paris', 'Hamburg'),
        ('Riga', 'Stockholm'),
        ('Hamburg', 'Barcelona'),
        ('Vienna', 'Barcelona'),
        ('Krakow', 'Vienna'),
        ('Riga', 'Hamburg'),
        ('Barcelona', 'Edinburgh'),
        ('Paris', 'Barcelona'),
        ('Hamburg', 'Edinburgh'),
        ('Paris', 'Vienna'),
        ('Vienna', 'Riga')
    ]
    allowed_edges = set()
    for a, b in direct_flights_pairs:
        a_int = city_to_int[a]
        b_int = city_to_int[b]
        allowed_edges.add((a_int, b_int))
        allowed_edges.add((b_int, a_int))
    
    s = Solver()
    
    # Variables for the cities at positions 1 to 6 (each can be 2 to 7)
    s1 = Int('s1')
    s2 = Int('s2')
    s3 = Int('s3')
    s4 = Int('s4')
    s5 = Int('s5')
    s6 = Int('s6')
    s_vars = [s1, s2, s3, s4, s5, s6]
    
    # Each s_i must be between 2 and 7 (inclusive)
    for var in s_vars:
        s.add(var >= 2)
        s.add(var <= 7)
    
    # All s_i must be distinct
    s.add(Distinct(s1, s2, s3, s4, s5, s6))
    
    # Entire sequence of cities (as integers)
    seq_int = [0] + s_vars + [1]  # [Paris, s1, s2, s3, s4, s5, s6, Stockholm]
    
    # Variables for end days: e0 is fixed to 2, e6 is fixed to 15.
    # We need e1, e2, e3, e4, e5 (for positions 1 to 5) and e6=15.
    e1 = Int('e1')
    e2 = Int('e2')
    e3 = Int('e3')
    e4 = Int('e4')
    e5 = Int('e5')
    e_vars = [e1, e2, e3, e4, e5]
    e0 = 2
    e6 = 15
    
    # End days must be non-decreasing: e0=2 <= e1 <= e2 <= e3 <= e4 <= e5 <= e6=15
    s.add(e1 >= e0)
    s.add(e2 >= e1)
    s.add(e3 >= e2)
    s.add(e4 >= e3)
    s.add(e5 >= e4)
    s.add(e6 >= e5)
    for e in e_vars:
        s.add(e >= e0, e <= e6)
    
    # Hamburg must be at one of the positions 2,3,4,5 (sequence indices 2,3,4,5)
    s.add(Or(
        seq_int[2] == 7,
        seq_int[3] == 7,
        seq_int[4] == 7,
        seq_int[5] == 7
    ))
    
    # Constraints for Hamburg: if at position j (2,3,4,5), then set e_{j-1}=10 and e_j=11
    # Note: seq_int[2] is the city at position2 (which is the third city, index2 in the sequence of 8)
    # For j=2: set e1=10 and e2=11
    # For j=3: set e2=10 and e3=11
    # For j=4: set e3=10 and e4=11
    # For j=5: set e4=10 and e5=11
    s.add(If(seq_int[2] == 7, And(e1 == 10, e2 == 11), True))
    s.add(If(seq_int[3] == 7, And(e2 == 10, e3 == 11), True))
    s.add(If(seq_int[4] == 7, And(e3 == 10, e4 == 11), True))
    s.add(If(seq_int[5] == 7, And(e4 == 10, e5 == 11), True))
    
    # For each position j in 1 to 6 (sequence indices 1 to 6), set the length constraint
    # and the Edinburgh constraint
    for j in range(1, 7):  # j from 1 to 6: positions in the sequence (index1 to index6)
        city_var = seq_int[j]
        # Length constraint:
        if j == 1:
            length = e1 - e0 + 1
        elif j == 2:
            length = e2 - e1 + 1
        elif j == 3:
            length = e3 - e2 + 1
        elif j == 4:
            length = e4 - e3 + 1
        elif j == 5:
            length = e5 - e4 + 1
        else:  # j==6
            length = e6 - e5 + 1
        # For every city at this position, the length must equal req_days[city]
        s.add(If(city_var == 2, length == req_days[2], True))
        s.add(If(city_var == 3, length == req_days[3], True))
        s.add(If(city_var == 4, length == req_days[4], True))
        s.add(If(city_var == 5, length == req_days[5], True))
        s.add(If(city_var == 6, length == req_days[6], True))
        s.add(If(city_var == 7, length == req_days[7], True))
        
        # Edinburgh constraint: if the city is Edinburgh (4), then the end day must be >=12
        if j == 1:
            end_day = e1
        elif j == 2:
            end_day = e2
        elif j == 3:
            end_day = e3
        elif j == 4:
            end_day = e4
        elif j == 5:
            end_day = e5
        else:  # j==6
            end_day = e6
        s.add(If(city_var == 4, end_day >= 12, True))
    
    # Flight constraints: for consecutive pairs in the sequence
    for i in range(0, 7):  # i from 0 to 6: pairs (0,1), (1,2), ... (6,7)
        a = seq_int[i]
        b = seq_int[i+1]
        # Allowed edge: (a,b) must be in allowed_edges
        edge_constraints = []
        for (x, y) in allowed_edges:
            edge_constraints.append(And(a == x, b == y))
        s.add(Or(edge_constraints))
    
    # Check and get the model
    if s.check() == sat:
        model = s.model()
        # Get the values for s1..s6
        s_vals = [model.evaluate(var).as_long() for var in s_vars]
        e_vals = [model.evaluate(var).as_long() for var in e_vars]
        
        # Build the entire sequence of city integers
        seq_city_ints = [0]  # Paris
        seq_city_ints.extend(s_vals)
        seq_city_ints.append(1)  # Stockholm
        city_names = [int_to_city[i] for i in seq_city_ints]
        
        # End days for positions 0 to 6: 
        # position0: e0=2
        # position1: e1
        # position2: e2
        # position3: e3
        # position4: e4
        # position5: e5
        # position6: e6=15
        end_days = [2] + e_vals + [15]  # [e0, e1, e2, e3, e4, e5, e6]
        
        # Build itinerary
        itinerary = []
        for i in range(0, 8):  # for each city in the sequence
            city = city_names[i]
            if i == 0:
                start = 1
                end = end_days[0]  # e0
            elif i < 7:
                start = end_days[i-1]
                end = end_days[i]
            else:  # i==7 (last city: Stockholm)
                start = end_days[6]  # e6=15
                end = 16
                
            # Format day range for the continuous stay
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary.append({"day_range": day_range_str, "place": city})
            
            # If not the last city, add the flight day records
            if i < 7:
                # On the end day, we are in the current city (departure) and the next city (arrival)
                day_str = f"Day {end}"
                itinerary.append({"day_range": day_str, "place": city})
                itinerary.append({"day_range": day_str, "place": city_names[i+1]})
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(result)
    else:
        print("No solution found")

if __name__ == "__main__":
    main()