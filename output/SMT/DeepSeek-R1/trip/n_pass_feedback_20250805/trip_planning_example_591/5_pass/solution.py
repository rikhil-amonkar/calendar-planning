from z3 import *

def main():
    city_names = ['Stuttgart', 'Bucharest', 'Geneva', 'Valencia', 'Munich']
    flight_pairs = [(2,4), (4,3), (1,3), (4,1), (3,0), (2,3)]
    allowed_set = set()
    for (i, j) in flight_pairs:
        allowed_set.add((i, j))
        allowed_set.add((j, i))
    
    s0, s1, s2, s3, s4 = Ints('s0 s1 s2 s3 s4')
    s = [s0, s1, s2, s3, s4]
    solver = Solver()
    
    # Ensure cities are distinct indices 0-4
    for i in range(5):
        solver.add(s[i] >= 0, s[i] <= 4)
    solver.add(Distinct(s0, s1, s2, s3, s4))
    
    # Flight constraints between consecutive cities
    for i in range(4):
        si = s[i]
        sj = s[i+1]
        solver.add(Or([And(si == p0, sj == p1) for (p0, p1) in allowed_set]))
    
    # Define duration lookup function
    def dur(city_idx):
        durations = {0: 2, 1: 2, 2: 4, 3: 6, 4: 7}
        return durations.get(city_idx, 0)
    
    # Arrival days
    a0 = Int('a0')
    a1 = Int('a1')
    a2 = Int('a2')
    a3 = Int('a3')
    a4 = Int('a4')
    a = [a0, a1, a2, a3, a4]
    solver.add(a0 == 1)
    for i in range(1, 5):
        solver.add(a[i] == a[i-1] + dur(s[i-1]) - 1)
    
    # Total trip must be 17 days
    last_day = a4 + dur(s4) - 1
    solver.add(last_day == 17)
    
    # Geneva must start on day 1, Munich on day 4
    for i in range(5):
        solver.add(If(s[i] == 2, a[i] == 1, True))
        solver.add(If(s[i] == 4, a[i] == 4, True))
    
    if solver.check() == sat:
        model = solver.model()
        seq_val = [model.evaluate(s[i]).as_long() for i in range(5)]
        a_val = [model.evaluate(a[i]).as_long() for i in range(5)]
        durations = [2, 2, 4, 6, 7]
        
        # Build day-to-places mapping
        day_to_places = []
        for day in range(1, 18):
            cities = []
            for i in range(5):
                start = a_val[i]
                end = start + durations[seq_val[i]] - 1
                if start <= day <= end:
                    cities.append(city_names[seq_val[i]])
            day_to_places.append(tuple(sorted(cities)))
        
        # Group consecutive days with same cities
        itinerary = []
        start_idx = 0
        current_places = day_to_places[0]
        for day in range(1, 17):
            if day_to_places[day] != current_places:
                if start_idx == day - 1:
                    day_range = f"Day {start_idx+1}"
                else:
                    day_range = f"Day {start_idx+1}-{day}"
                itinerary.append({
                    'day_range': day_range,
                    'place': ', '.join(current_places)
                })
                start_idx = day
                current_places = day_to_places[day]
        
        # Add last group
        if start_idx == 16:
            day_range = "Day 17"
        else:
            day_range = f"Day {start_idx+1}-17"
        itinerary.append({
            'day_range': day_range,
            'place': ', '.join(day_to_places[16])
        })
        
        # Print result
        import json
        result = {'itinerary': itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()