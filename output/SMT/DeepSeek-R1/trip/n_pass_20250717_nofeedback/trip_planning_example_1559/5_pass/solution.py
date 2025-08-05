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

    # Location at start of each day (0-indexed days 0-24)
    L = [Int(f'L_{i}') for i in range(25)]
    for i in range(25):
        s.add(L[i] >= 0, L[i] < 10)

    # Flight indicators for end of each day
    fly = [Bool(f'fly_{i}') for i in range(24)]

    # Flight constraints
    for i in range(24):
        valid_flight = Or([And(L[i] == a, L[i+1] == b) for a, b in directed_edges])
        s.add(If(fly[i], valid_flight, L[i] == L[i+1]))
    
    # Presence in cities matrix (0-indexed days 0-24)
    In = [[Bool(f'In_{d}_{c}') for c in range(10)] for d in range(25)]
    
    for d in range(25):
        if d < 24:
            for c in range(10):
                # In city c on day d if:
                # 1. Start day in city c, OR
                # 2. Flight from another city to c at end of day
                s.add(In[d][c] == Or(L[d] == c, And(fly[d], L[d+1] == c))
        else:  # Last day only depends on start location
            for c in range(10):
                s.add(In[d][c] == (L[d] == c))
    
    # Required days per city
    for c in range(10):
        total_days = Sum([If(In[d][c], 1, 0) for d in range(25)])
        s.add(total_days == required_days[c])
    
    # Event constraints (1-indexed days mapped to 0-indexed)
    # Valencia must be on day 3 or 4 (1-indexed) → days 2-3 (0-indexed)
    s.add(Or(In[2][0], In[3][0]))
    # Oslo must be on day 13,14, or15 (1-indexed) → days 12-14 (0-indexed)
    s.add(Or(In[12][1], In[13][1], In[14][1]))
    # Seville between day 5-9 (1-indexed) → days 4-8 (0-indexed)
    s.add(Or([In[d][6] for d in range(4, 9)))
    # Mykonos between day 21-25 (1-indexed) → days 20-24 (0-indexed)
    s.add(Or([In[d][8] for d in range(20, 25)))
    
    if s.check() == sat:
        m = s.model()
        loc_assignments = [m.eval(L[i]).as_long() for i in range(25)]
        fly_assignments = [is_true(m.eval(fly[i])) for i in range(24)]
        
        # Build itinerary with 1-indexed days
        stays = []
        current_city_idx = loc_assignments[0]
        start_day = 1  # 1-indexed
        for i in range(24):
            if fly_assignments[i]:
                end_day = i + 1  # 1-indexed end day
                stays.append((cities[current_city_idx], start_day, end_day))
                current_city_idx = loc_assignments[i+1]
                start_day = i + 1  # Next city starts same day
        stays.append((cities[current_city_idx], start_day, 25))
        
        # Format itinerary
        itinerary_list = []
        for city, start, end in stays:
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