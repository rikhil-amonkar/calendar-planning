from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Paris', 'Naples', 'Zurich', 'Lyon', 'Nice', 'Riga', 'Stockholm', 'Seville']
    durations = [1, 2, 4, 3, 4, 2, 1, 2, 2, 2]
    num_cities = len(cities)
    total_days = 23

    s = Solver()

    # Start and end days for each city
    starts = [Int(f'start_{c}') for c in cities]
    ends = [Int(f'end_{c}') for c in cities]
    
    # Ensure valid start/end days and correct durations
    for i in range(num_cities):
        s.add(starts[i] >= 1, starts[i] <= total_days)
        s.add(ends[i] == starts[i] + durations[i] - 1)
        s.add(ends[i] <= total_days, ends[i] >= 1)
    
    # No overlapping stays
    for i in range(num_cities):
        for j in range(i + 1, num_cities):
            # One city must end before the other starts
            s.add(Or(
                ends[i] < starts[j],
                ends[j] < starts[i]
            ))
    
    # All days must be covered
    for day in range(1, total_days + 1):
        covered = Or([And(starts[i] <= day, day <= ends[i]) for i in range(num_cities)])
        s.add(covered)
    
    # Solve and extract solution
    if s.check() == sat:
        m = s.model()
        blocks = []
        for i in range(num_cities):
            start_val = m.evaluate(starts[i]).as_long()
            end_val = m.evaluate(ends[i]).as_long()
            blocks.append((start_val, end_val, cities[i]))
        
        # Sort by start day
        blocks.sort(key=lambda x: x[0])
        
        # Verify contiguous coverage
        last_end = 0
        for start, end, city in blocks:
            if start != last_end + 1 and last_end != 0:
                print(f"Gap between {last_end} and {start}")
            last_end = end
        
        itinerary = []
        for start, end, city in blocks:
            if start == end:
                day_range = f"Day {start}"
            else:
                day_range = f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': city})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()