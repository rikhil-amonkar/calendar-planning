from z3 import Solver, Int, sat

def main():
    s = Solver()
    cities = ['Rome', 'Mykonos', 'Nice', 'Riga', 'Bucharest', 'Munich', 'Krakow']
    min_days = [3, 2, 2, 1, 3, 3, 1]
    max_days = [4, 3, 3, 3, 4, 4, 2]
    
    # Duration variables for each city
    d = [Int(f'd_{city}') for city in cities]
    
    # Constrain durations to be within min/max
    for i in range(len(cities)):
        s.add(d[i] >= min_days[i])
        s.add(d[i] <= max_days[i])
    
    # Cumulative days counter
    cumulative = 0
    starts = []
    ends = []
    
    # Build start/end positions based on durations
    for i in range(len(cities)):
        if i == 0:
            start_val = 1
        else:
            start_val = cumulative + 1  # Start immediately after previous city
        end_val = cumulative + d[i]      # End after current duration
        starts.append(start_val)
        ends.append(end_val)
        cumulative += d[i]
    
    # Total trip must be exactly 17 days
    s.add(cumulative == 17)
    
    if s.check() == sat:
        m = s.model()
        # Evaluate durations
        d_vals = [m.eval(d[i]).as_long() for i in range(len(cities))]
        
        # Recalculate start/end using actual durations
        cumulative = 0
        itinerary = []
        for i in range(len(cities)):
            if i == 0:
                start_val = 1
            else:
                start_val = cumulative + 1
            end_val = cumulative + d_vals[i]
            cumulative += d_vals[i]
            
            # Format day range
            if start_val == end_val:
                day_range = f'Day {start_val}'
            else:
                day_range = f'Day {start_val}-{end_val}'
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()