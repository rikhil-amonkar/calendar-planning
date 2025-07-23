from z3 import *
import json

def main():
    cities = ['Valencia', 'Oslo', 'Lyon', 'Prague', 'Paris', 'Nice', 'Seville', 'Tallinn', 'Mykonos', 'Lisbon']
    required_days = [2, 3, 4, 3, 4, 4, 5, 2, 5, 2]

    directed_edges = [
        (9,4), (4,9), # Lisbon and Paris
        (2,5), (5,2), # Lyon and Nice
        (7,1), (1,7), # Tallinn and Oslo
        (3,2), (2,3), # Prague and Lyon
        (4,1), (1,4), # Paris and Oslo
        (9,6), (6,9), # Lisbon and Seville
        (3,9), (9,3), # Prague and Lisbon
        (1,5), (5,1), # Oslo and Nice
        (0,4), (4,0), # Valencia and Paris
        (0,9), (9,0), # Valencia and Lisbon
        (4,5), (5,4), # Paris and Nice
        (5,8), (8,5), # Nice and Mykonos
        (4,2), (2,4), # Paris and Lyon
        (0,2), (2,0), # Valencia and Lyon
        (3,1), (1,3), # Prague and Oslo
        (3,4), (4,3), # Prague and Paris
        (6,4), (4,6), # Seville and Paris
        (1,2), (2,1), # Oslo and Lyon
        (3,0), (0,3), # Prague and Valencia
        (9,5), (5,9), # Lisbon and Nice
        (9,1), (1,9), # Lisbon and Oslo
        (0,6), (6,0), # Valencia and Seville
        (9,2), (2,9), # Lisbon and Lyon
        (4,7), (7,4), # Paris and Tallinn
        (3,7), (7,3)  # Prague and Tallinn
    ]

    s = Solver()

    # L[i] = city index at the start of day i (0-indexed days 0..24)
    L = [Int(f'L_{i}') for i in range(25)]
    for i in range(25):
        s.add(L[i] >= 0, L[i] < 10)

    # fly[i] = whether we fly at the end of day i (0-indexed i=0..23)
    fly = [Bool(f'fly_{i}') for i in range(24)]

    # Flight constraints: if fly[i], then (L[i], L[i+1]) must be a directed edge
    for i in range(24):
        edge_constraints = []
        for a, b in directed_edges:
            edge_constraints.append(And(L[i] == a, L[i+1] == b))
        s.add(If(fly[i], Or(edge_constraints), L[i] == L[i+1]))
    
    # Create C: the city for each day (1-25). Each day can be in multiple cities?
    # Instead, we define an auxiliary variable for each day: the set of cities it belongs to?
    # But we need to count the days per city. We'll define a 2D array: In[day][city] = Bool
    # But we have 25 days and 10 cities -> 250 variables, which is acceptable.
    In = [[Bool(f'In_{d}_{c}') for c in range(10)] for d in range(25)]
    
    # For each day d (0-indexed for 0..24, representing day1..day25)
    for d in range(25):
        # The day starts in L[d]
        # If d < 24 and we fly at the end of this day (fly[d]), then we also belong to L[d+1] (the next day's start city)
        # Otherwise, we only belong to L[d]
        for c in range(10):
            # If we are at the last day (d=24), then we don't fly after, so only L[24]
            if d == 24:
                s.add(In[d][c] == (L[d] == c))
            else:
                # In[d][c] is true if either:
                #   (a) L[d] == c (the start city of the day is c), OR
                #   (b) fly[d] is True and L[d+1] == c (the next day's start city is c)
                s.add(In[d][c] == Or(L[d] == c, And(fly[d], L[d+1] == c)))
    
    # Now, for each city, the number of days it appears in some In[d][c] should equal required_days[c]
    for c in range(10):
        total_days = 0
        for d in range(25):
            total_days += If(In[d][c], 1, 0)
        s.add(total_days == required_days[c])
    
    # Event constraints: 
    # Valencia (index0) must be on day 3 or 4 (which are d=2 or d=3 in 0-indexed days)
    s.add(Or(In[2][0], In[3][0]))
    # Oslo (index1) must be on day 13, 14, or 15 (d=12,13,14)
    s.add(Or(In[12][1], In[13][1], In[14][1]))
    # Seville (index6) must be between day 5 and 9 (d=4 to 8)
    s.add(Or([In[d][6] for d in range(4,9)]))
    # Mykonos (index8) must be between day 21 and 25 (d=20 to 24)
    s.add(Or([In[d][8] for d in range(20,25)]))
    
    if s.check() == sat:
        m = s.model()
        # Get the assignments for L and fly
        loc_assignments = [m.eval(L[i]).as_long() for i in range(25)]
        fly_assignments = [is_true(m.eval(fly[i])) for i in range(24)]
        
        # Build itinerary: group consecutive days that are in the same city?
        # But note: a flight day d (0-indexed) means that day d+1 (1-indexed) is in two cities: the departure (L[d]) and arrival (L[d+1])
        # How to represent? We want to show the stay in a city as a continuous range, but with overlapping days for flight days.
        
        # Instead, we'll use the In matrix to see which cities are present on each day?
        # But that would be complex for grouping.
        
        # Alternative: use the loc_assignments and fly_assignments to build stays, but with the understanding that:
        #   When we fly at the end of day i, day i+1 (1-indexed) is the first day of the next city and also the last day of the current city is day i+1.
        # We'll build:
        #   Start with city0 = cities[loc_assignments[0]], start_day = 1
        #   For i from 0 to 23:
        #       if fly_assignments[i] is True, then we end the current stay at day i+1 (because flight at end of day i makes day i+1 the last day of current city)
        #          and start a new city at day i+1 (the same day) for the next city.
        #   Then the last city goes until day25.
        
        stays = []
        current_city_idx = loc_assignments[0]
        start_day = 1
        for i in range(24):
            if fly_assignments[i]:
                # Flight at the end of day i (0-indexed), which is after day i+1 (1-indexed) starts? 
                # This flight means that the next day (i+2 in 1-indexed) we start in a new city, but day i+1 (1-indexed) is the last day of current city and first day of next.
                # We end the current city at day i+1
                end_day = i+1
                stays.append((cities[current_city_idx], start_day, end_day))
                # The next city starts on the same day? 
                current_city_idx = loc_assignments[i+1]
                start_day = i+1   # same day as the end of the previous stay
        # Last stay: from start_day to 25
        stays.append((cities[current_city_idx], start_day, 25))
        
        # Now, represent the itinerary
        itinerary_list = []
        for stay in stays:
            city, start, end = stay
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary_list.append({'day_range': day_range, 'place': city})
        
        result = {'itinerary': itinerary_list}
        print(json.dumps(result))
    else:
        print("No solution found")

if __name__ == '__main__':
    main()