from z3 import Solver, Int, sat

def main():
    s = Solver()
    cities = ['Rome', 'Mykonos', 'Nice', 'Riga', 'Bucharest', 'Munich', 'Krakow']
    min_days = [3, 2, 2, 1, 3, 3, 1]
    max_days = [4, 3, 3, 3, 4, 4, 2]
    
    starts = [Int(f'start_{city}') for city in cities]
    durations = [Int(f'duration_{city}') for city in cities]
    ends = [Int(f'end_{city}') for city in cities]
    
    # Fixed start and end constraints
    s.add(starts[0] == 1)
    s.add(ends[-1] == 17)
    
    # Define relationships between starts, durations, and ends
    for i in range(len(cities)):
        s.add(ends[i] == starts[i] + durations[i] - 1)
        s.add(durations[i] >= min_days[i])
        s.add(durations[i] <= max_days[i])
        s.add(starts[i] >= 1)
        s.add(ends[i] <= 17)
    
    # Consecutive transition constraints
    for i in range(len(cities)-1):
        s.add(starts[i+1] == ends[i] + 1)
    
    if s.check() == sat:
        m = s.model()
        start_vals = [m.eval(starts[i]).as_long() for i in range(len(cities))]
        end_vals = [m.eval(ends[i]).as_long() for i in range(len(cities))]
        itinerary = []
        for i in range(len(cities)):
            s_val = start_vals[i]
            e_val = end_vals[i]
            if s_val == e_val:
                day_range = f'Day {s_val}'
            else:
                day_range = f'Day {s_val}-{e_val}'
            itinerary.append({'day_range': day_range, 'place': cities[i]})
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()