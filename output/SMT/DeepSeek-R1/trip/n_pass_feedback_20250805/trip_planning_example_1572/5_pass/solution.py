from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Paris', 'Naples', 'Zurich', 'Lyon', 'Nice', 'Riga', 'Stockholm', 'Seville']
    durations = [1, 2, 4, 3, 4, 2, 1, 2, 2, 2]
    num_cities = len(cities)
    total_days = 23

    s = Solver()

    # Position of each city in the sequence (0 to num_cities-1)
    positions = [Int(f'pos_{c}') for c in cities]
    for pos in positions:
        s.add(pos >= 0, pos < num_cities)
    s.add(Distinct(positions))

    # Start and end days for each city
    starts = [Int(f'start_{c}') for c in cities]
    ends = [Int(f'end_{c}') for c in cities]

    for i in range(num_cities):
        # Calculate total duration of cities before this one
        before_sum = sum([If(positions[j] < positions[i], durations[j], 0) for j in range(num_cities)])
        s.add(starts[i] == 1 + before_sum)
        s.add(ends[i] == starts[i] + durations[i] - 1)

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