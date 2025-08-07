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

    order = [Int(f'order_{i}') for i in range(n)]
    start = [Int(f'start_{i}') for i in range(n)]
    end = [Int(f'end_{i}') for i in range(n)]  # Now represents exclusive end

    for i in range(n):
        s.add(order[i] >= 0, order[i] < n)
    s.add(Distinct(order))

    dur_arr = Array('dur_arr', IntSort(), IntSort())
    for idx, d in enumerate(durations):
        s.add(dur_arr[idx] == d)

    s.add(start[0] == 1)
    s.add(end[n-1] == 27)  # Exclusive end of last day = 27

    for i in range(n):
        dur_i = dur_arr[order[i]]
        s.add(end[i] == start[i] + dur_i)  # Exclusive end = start + duration

    for i in range(n-1):
        s.add(start[i+1] == end[i])  # Next starts where previous ends

    for i in range(n):
        s.add(start[i] >= 1, end[i] <= 27)
        s.add(start[i] < end[i])

    if s.check() == sat:
        m = s.model()
        itinerary = []
        for i in range(n):
            idx_val = m.evaluate(order[i]).as_long()
            city = cities[idx_val]
            start_val = m.evaluate(start[i]).as_long()
            end_val = m.evaluate(end[i]).as_long()
            day_range = f'Day {start_val}-{end_val-1}'  # Convert to inclusive
            itinerary.append({'day_range': day_range, 'place': city})
        plan = {'itinerary': itinerary}
        print(f"Plan found: {plan}")
    else:
        print("No valid plan found")

if __name__ == '__main__':
    main()