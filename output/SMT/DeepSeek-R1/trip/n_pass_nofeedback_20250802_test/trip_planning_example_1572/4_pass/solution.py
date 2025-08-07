from z3 import *

def main():
    cities_list = ['Berlin', 'Munich', 'Hamburg', 'Frankfurt', 'Cologne', 'Stuttgart', 'Paris', 'Lyon', 'Nice', 'Milan', 
                  'Rome', 'Naples', 'Barcelona', 'Madrid', 'Seville', 'Valencia', 'Athens', 'Budapest', 'Vienna', 'Prague', 
                  'Zurich', 'Geneva', 'Amsterdam', 'Brussels', 'Copenhagen', 'Stockholm', 'Helsinki', 'Oslo', 'Riga', 'Warsaw']
    
    n_stops = 11
    s = Solver()
    
    # City index variables for 11 stops
    c = [Int(f'c_{i}') for i in range(n_stops)]
    
    # First and last must be Berlin (index 0)
    s.add(c[0] == 0)
    s.add(c[10] == 0)
    
    # Valid city indices for all stops
    for i in range(n_stops):
        s.add(c[i] >= 0, c[i] < len(cities_list))
    
    # Middle 9 cities distinct and not Berlin
    s.add(Distinct([c[i] for i in range(1, 10)]))
    for i in range(1, 10):
        s.add(c[i] != 0)
    
    # Consecutive cities must be different
    for i in range(10):
        s.add(c[i] != c[i+1])
    
    # Fixed stay durations: first/last Berlin=2 days, intermediates=1 day
    durations = [2] + [1]*9 + [2]
    
    # Precomputed day ranges accounting for travel days
    day_ranges = [
        "Day 1-2",    # Berlin (2 days)
        "Day 4",       # After travel day on Day 3
        "Day 6",       # After travel day on Day 5
        "Day 8",       # After travel day on Day 7
        "Day 10",      # After travel day on Day 9
        "Day 12",      # After travel day on Day 11
        "Day 14",      # After travel day on Day 13
        "Day 16",      # After travel day on Day 15
        "Day 18",      # After travel day on Day 17
        "Day 20",      # After travel day on Day 19
        "Day 22-23"    # Berlin (2 days after travel on Day 21)
    ]
    
    if s.check() == sat:
        m = s.model()
        c_val = [m.evaluate(c[i]).as_long() for i in range(n_stops)]
        
        itinerary = []
        for i in range(n_stops):
            itinerary.append({
                'day_range': day_ranges[i],
                'place': cities_list[c_val[i]]
            })
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == "__main__":
    main()