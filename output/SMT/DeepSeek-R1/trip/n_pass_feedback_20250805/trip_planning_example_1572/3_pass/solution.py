from z3 import *

def main():
    cities = ['Berlin', 'Milan', 'Paris', 'Naples', 'Zurich', 'Lyon', 'Nice', 'Riga', 'Stockholm', 'Seville']
    durations = [1, 2, 4, 3, 4, 2, 1, 2, 2, 2]
    num_cities = len(cities)
    total_days = 23

    s = Solver()

    # Day assignment array: city index for each day (0-indexed days 0-22 represent days 1-23)
    city_on_day = [Int(f'city_day_{d}') for d in range(total_days)]
    for d in range(total_days):
        s.add(city_on_day[d] >= 0, city_on_day[d] < num_cities)

    # Start and end day for each city
    starts = [Int(f'start_{c}') for c in cities]
    ends = [Int(f'end_{c}') for c in cities]

    for i in range(num_cities):
        # Start between 1-23, end = start + duration - 1
        s.add(starts[i] >= 1, starts[i] <= total_days)
        s.add(ends[i] == starts[i] + durations[i] - 1)
        s.add(ends[i] <= total_days)

        # Ensure city occupies correct days and no others
        for d in range(total_days):
            day_num = d + 1  # actual calendar day
            in_interval = And(day_num >= starts[i], day_num <= ends[i])
            s.add(If(in_interval, city_on_day[d] == i, city_on_day[d] != i))

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
            day_range = f"Day {start}" if start == end else f"Day {start}-{end}"
            itinerary.append({'day_range': day_range, 'place': city})
        
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()