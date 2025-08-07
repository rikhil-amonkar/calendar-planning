from z3 import *

def main():
    city_durations = {
        'Lyon': 3,
        'Venice': 3,
        'Copenhagen': 3,
        'Barcelona': 3,
        'Reykjavik': 3,
        'Dubrovnik': 4,
        'Munich': 3,
        'Tallinn': 4
    }
    cities = list(city_durations.keys())
    durations = [city_durations[c] for c in cities]
    n = len(cities)

    s = Solver()

    # City order as indices
    order = [Int(f'order_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]

    # Ensure valid and distinct city indices
    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))

    # Create duration array
    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        s.add(dur_arr[idx] == d)

    # Trip must start on day 1 and end on day 26
    s.add(start[0] == 1)
    s.add(end[n-1] == 26)

    # Duration constraints using array selection
    for i in range(n):
        dur_i = dur_arr[order[i]]
        s.add(end[i] == start[i] + dur_i - 1)

    # Consecutive cities must be contiguous
    for i in range(n-1):
        s.add(end[i] + 1 == start[i+1])

    # Validate day ranges
    for i in range(n):
        s.add(start[i] >= 1, end[i] <= 26)
        s.add(start[i] <= end[i])

    # Total trip must be exactly 26 days
    total_days = end[n-1] - start[0] + 1
    s.add(total_days == 26)

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            idx_val = m.evaluate(order[i]).as_long()
            city = cities[idx_val]
            start_val = m.evaluate(start[i]).as_long()
            end_val = m.evaluate(end[i]).as_long()
            day_range = f'Day {start_val}-{end_val}'
            itinerary.append({'day_range': day_range, 'place': city})
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()